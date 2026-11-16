-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_23
-- name    : ARTreeCover.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:08:39.472913+00:00
-- url     : https://prove2.me/theorems/bfd57222-4ffc-4262-bffc-29794f6851b0
-- title:
--   Theorem 23 — doubling and bounded-highway-dimension graphs have spanning almost-Ramsey tree covers and almost-Ramsey HST covers (corrected: $d,h$ read as $\max(1,d),\max(1,h)$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted graph, $k\ge1$ an integer, $0<\epsilon\le1$ and $L(n)=\max(1,\log_2n)$.
--
--   1. If $G$ has doubling dimension at most $d$, it admits a spanning almost-Ramsey tree cover and an almost-Ramsey HST cover, both with stretch $Ck$ and size at most $C\max(1,d)^{1/k}L(n)^2$.
--   2. If $G$ has $(1+\epsilon)$-highway dimension at most $h$, it admits a spanning almost-Ramsey tree cover and an almost-Ramsey HST cover, both with stretch $C/\epsilon$ and size at most $C\max(1,h)^2L(n)$; and also such covers with stretch $Ck$ and size at most
--   $$C\max(1,h)^{1/k}L(n)^2.$$
--
--   The trees are spanning trees of $G$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: d^{1/k} (doubling dimension at most d) inside O(·) → max(1, d)^{1/k}; reason: a one-vertex graph has doubling dimension 0, and with d = 0 the bound d^{1/k} = 0 allows no layer or tree, while a cover needs one; for d ≥ 1 nothing changes
--   - correction: h(ϵ) inside O(·) and Ω(·) → max(1, h); reason: a one-vertex graph has highway dimension 0, and with h = 0 the size bound is 0 (no tree) or the count divides by 0; for h ≥ 1 nothing changes
--   - reading: (1 + ϵ)-highway dimension at most h(ϵ) → Definition 9 at the theorem's own ϵ, with h = h(ϵ) ∈ ℕ; reason: the conclusion involves only h(ϵ); this reading is the weaker hypothesis, hence the stronger theorem
--   - encoding: almost-Ramsey forest/HST cover with stretch α → the cover predicate, the stretch predicate and the almost-Ramsey predicate with the same α; reason: almost-Ramsey with stretch α implies stretch α (take ∆ = d_G(u, v)); the published theorem_19 uses the same encoding
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 23, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover
import Definitions.Def_ARTreeCover_Supplement_DoublingDimLE
import Definitions.Def_ARTreeCover_Supplement_HighwayDimLE

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 23**, p.36 (PDF p.39). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be a connected n-vertex graph, let k ≥ 1 be an integer parameter, and let
0 < ϵ ≤ 1 be a real parameter.
1. If G has doubling dimension at most d, it admits a spanning almost-Ramsey tree cover and an
almost-Ramsey HST cover, both with stretch O(k) and size O(d^{1/k} log² n).
2. If G has (1 + ϵ)-highway dimension at most h(ϵ), it admits a spanning almost-Ramsey tree cover and
an almost-Ramsey HST cover, both with stretch O(1/ϵ) and size O(h(ϵ)² · log n). It also admits such
covers with stretch O(k) and size O(h(ϵ)^{1/k} · log² n)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·).
   `L(n) = max(1, log₂ n)`.
2. `d` and `h` are clamped to `max(1, ·)` inside O(·): a one-vertex graph has doubling dimension
   `0` and highway dimension `0`, and a cover needs at least one tree.
3. The highway hypothesis is Definition 9 at this `ϵ` with `h = h(ϵ) ∈ ℕ` (`HighwayDimLE G ε h`).
4. Spanning trees are spanning `WForest`s whose graph is `SimpleGraph.IsTree`, as in the published
   `theorem_19`; almost-Ramsey covers are also stated with stretch. -/
theorem theorem_23 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (k : ℕ) (ε : ℝ),
        1 ≤ k → 0 < ε → ε ≤ 1 → G.graph.Connected →
        (∀ d : ℝ, DoublingDimLE G d →
          ((∃ m : ℕ, (m : ℝ) ≤ C * (max 1 d) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ T : Fin m → WForest V,
              (∀ i, (T i).graph.IsTree ∧ (T i).IsSpanning G) ∧
              IsForestCover G T ∧
              ForestStretchLE G T (C * k) ∧
              ForestAlmostRamsey G T (C * k)) ∧
            (∃ m : ℕ, (m : ℝ) ≤ C * (max 1 d) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ H : Fin m → HST V,
              IsHSTCover G H ∧
              HSTStretchLE G H (C * k) ∧
              HSTAlmostRamsey G H (C * k)))) ∧
        (∀ h : ℕ, HighwayDimLE G ε h →
          ((∃ m : ℕ, (m : ℝ) ≤ C * (max 1 (h : ℝ)) ^ 2 * logL (Fintype.card V) ∧ ∃ T : Fin m → WForest V,
              (∀ i, (T i).graph.IsTree ∧ (T i).IsSpanning G) ∧
              IsForestCover G T ∧
              ForestStretchLE G T (C / ε) ∧
              ForestAlmostRamsey G T (C / ε)) ∧
            (∃ m : ℕ, (m : ℝ) ≤ C * (max 1 (h : ℝ)) ^ 2 * logL (Fintype.card V) ∧ ∃ H : Fin m → HST V,
              IsHSTCover G H ∧
              HSTStretchLE G H (C / ε) ∧
              HSTAlmostRamsey G H (C / ε))) ∧
          ((∃ m : ℕ, (m : ℝ) ≤ C * (max 1 (h : ℝ)) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ T : Fin m → WForest V,
              (∀ i, (T i).graph.IsTree ∧ (T i).IsSpanning G) ∧
              IsForestCover G T ∧
              ForestStretchLE G T (C * k) ∧
              ForestAlmostRamsey G T (C * k)) ∧
            (∃ m : ℕ, (m : ℝ) ≤ C * (max 1 (h : ℝ)) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ H : Fin m → HST V,
              IsHSTCover G H ∧
              HSTStretchLE G H (C * k) ∧
              HSTAlmostRamsey G H (C * k)))) := by sorry

end ARTreeCover.Supplement
