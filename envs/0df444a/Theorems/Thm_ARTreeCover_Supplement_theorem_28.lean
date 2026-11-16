-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_28
-- name    : ARTreeCover.Supplement.theorem_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:11:42.044924+00:00
-- url     : https://prove2.me/theorems/604fb00f-6538-461c-b3f9-2f9c745bd32e
-- title:
--   Theorem 28 — connected doubling and bounded-highway-dimension graphs have spanning almost-Ramsey trees and HSTs (corrected: $O(1/\epsilon)$ clause for $\epsilon\le1$; $\max(1,\cdot)$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted graph, $k\ge1$ an integer, $\Delta,\epsilon>0$ and $L(n)=\max(1,\log_2n)$.
--
--   1. If $G$ has doubling dimension at most $d$, it has a spanning almost-Ramsey tree and an almost-Ramsey HST for scale $\Delta$, each satisfying at least $\dfrac{n}{C\max(1,d)^{1/k}L(n)}$ vertices with stretch $Ck$.
--   2. If $G$ has $(1+\epsilon)$-highway dimension at most $h$, then (a) if $\epsilon\le1$, it has a spanning almost-Ramsey tree and an almost-Ramsey HST satisfying at least $\dfrac{n}{C\max(1,h)^2}$ vertices with stretch $C/\epsilon$; and (b) it has a spanning almost-Ramsey tree and an almost-Ramsey HST satisfying at least
--   $$\frac{n}{C\max(1,h)^{1/k}L(n)}$$
--   vertices with stretch $Ck$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: d^{1/k} (doubling dimension at most d) inside O(·) → max(1, d)^{1/k}; reason: a one-vertex graph has doubling dimension 0, and with d = 0 the bound d^{1/k} = 0 allows no layer or tree, while a cover needs one; for d ≥ 1 nothing changes
--   - correction: h(ϵ) inside O(·) and Ω(·) → max(1, h); reason: a one-vertex graph has highway dimension 0, and with h = 0 the size bound is 0 (no tree) or the count divides by 0; for h ≥ 1 nothing changes
--   - reading: (1 + ϵ)-highway dimension at most h(ϵ) → Definition 9 at the theorem's own ϵ, with h = h(ϵ) ∈ ℕ; reason: the conclusion involves only h(ϵ); this reading is the weaker hypothesis, hence the stronger theorem
--   - correction: the stretch-O(1/ϵ) clause of item 2 for every ϵ > 0 → that clause for 0 < ϵ ≤ 1 only (the other clauses for every ϵ > 0); reason: as printed, for any C take the two-vertex graph with one edge of weight 1 (highway dimension at most 2) and ∆ = 1: a satisfied vertex u and the other vertex v need 1 = d_G(u, v) ≤ d_T(u, v) ≤ (C/ϵ)·1 < 1 once ϵ > C; the clause comes from Theorem 23, stated for ϵ ≤ 1, and h(ϵ) is not monotone in ϵ, so no clamp of ϵ is available
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 28, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_Supplement_DoublingDimLE
import Definitions.Def_ARTreeCover_Supplement_HighwayDimLE
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 28**, p.39 (PDF p.42). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G be a connected n-vertex graph, let k ≥ 1 be an integer parameter, and let ∆, ϵ > 0 be real
parameters.
1. If G has doubling dimension at most d, it admits a spanning almost-Ramsey tree and an
almost-Ramsey HST, that satisfy Ω(n/(d^{1/k} log n)) vertices with stretch O(k).
2. If G has (1+ϵ)-highway dimension at most h(ϵ), it admits a spanning almost-Ramsey tree and an
almost-Ramsey HST, that satisfy Ω(n/h(ϵ)²) vertices with stretch O(1/ϵ). It also admits a spanning
almost-Ramsey tree and an almost-Ramsey HST, that satisfy Ω(n/(h(ϵ)^{1/k} · log n)) vertices with
stretch O(k)."

**Formalization Note.**
1. `O(x)` is `C · x` and `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other
   parameter. `L(n) = max(1, log₂ n)`; `d`, `h` are clamped to `max(1, ·)`.
2. Correction: the first clause of item 2 (stretch `O(1/ϵ)`) is stated for `ϵ ≤ 1`, the range of
   Theorem 23 it rests on. For large `ϵ` the stretch `C/ϵ < 1` is impossible for two adjacent
   vertices at distance `∆`. The other clauses hold for every `ϵ > 0`.
3. The highway hypothesis is Definition 9 at this `ϵ` with `h = h(ϵ) ∈ ℕ`. -/
theorem theorem_28 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (k : ℕ) (Δ ε : ℝ),
        1 ≤ k → 0 < Δ → 0 < ε → G.graph.Connected →
        (∀ d : ℝ, DoublingDimLE G d →
          ((∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (max 1 d) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (max 1 d) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)))) ∧
        (∀ h : ℕ, HighwayDimLE G ε h →
          (ε ≤ 1 →
            ((∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (max 1 (h : ℝ)) ^ 2)) (C / ε)) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (max 1 (h : ℝ)) ^ 2)) (C / ε)))) ∧
          ((∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * (max 1 (h : ℝ)) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * (max 1 (h : ℝ)) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)))) := by sorry

end ARTreeCover.Supplement
