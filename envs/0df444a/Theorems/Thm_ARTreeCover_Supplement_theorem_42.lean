-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_42
-- name    : ARTreeCover.Supplement.theorem_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:14:32.416214+00:00
-- url     : https://prove2.me/theorems/e60c7e14-8cd9-437f-8c7c-d049aa2c7c87
-- title:
--   Theorem 42 — almost-Ramsey embeddings into $\ell_q^{O(\log n)}$ for doubling and bounded-highway-dimension graphs (corrected: $O(1/\epsilon)$ clause for $\epsilon\le1$; $\max(1,\cdot)$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted graph, $k\ge1$ an integer, $\Delta,\epsilon>0$, $q\in[1,\infty]$ and $L(n)=\max(1,\log_2n)$. In each case there are $D\le C\,L(n)$ and an almost-Ramsey embedding $f:V\to\ell_q^D$ for scale $\Delta$:
--
--   1. if $G$ has doubling dimension at most $d$: satisfying at least $\dfrac{n}{CL(n)}\max(1,d)^{-1/k}$ vertices with distortion $Ck$;
--   2. if $G$ has $(1+\epsilon)$-highway dimension at most $h$: (a) if $\epsilon\le1$, satisfying at least $\dfrac{n}{C\max(1,h)^2}$ vertices with distortion $C/\epsilon$; and (b) satisfying at least
--   $$\frac{n}{CL(n)}\max(1,h)^{-1/k}$$
--   vertices with distortion $Ck$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: ℓ_q^{O(log n)}, 1 ≤ q ≤ ∞ → PiLp q (Fin D → ℝ) with D ≤ C·L(n), q : ℝ≥0∞ with 1 ≤ q; reason: the same spaces; q = ∞ is the sup norm, and the dimension bound is uniform in q
--   - correction: d^{1/k} (doubling dimension at most d) inside O(·) → max(1, d)^{1/k}; reason: a one-vertex graph has doubling dimension 0, and with d = 0 the bound d^{1/k} = 0 allows no layer or tree, while a cover needs one; for d ≥ 1 nothing changes
--   - correction: h(ϵ) inside O(·) and Ω(·) → max(1, h); reason: a one-vertex graph has highway dimension 0, and with h = 0 the size bound is 0 (no tree) or the count divides by 0; for h ≥ 1 nothing changes
--   - reading: (1 + ϵ)-highway dimension at most h(ϵ) → Definition 9 at the theorem's own ϵ, with h = h(ϵ) ∈ ℕ; reason: the conclusion involves only h(ϵ); this reading is the weaker hypothesis, hence the stronger theorem
--   - correction: the stretch-O(1/ϵ) clause of item 2 for every ϵ > 0 → that clause for 0 < ϵ ≤ 1 only (the other clauses for every ϵ > 0); reason: as printed, for any C take the two-vertex graph with one edge of weight 1 (highway dimension at most 2) and ∆ = 1: a satisfied u and the other vertex v need 1 ≤ ‖f(u) − f(v)‖_q ≤ C/ϵ < 1 once ϵ > C; the clause rests on Theorem 23 (ϵ ≤ 1), and h(ϵ) is not monotone in ϵ
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 42, p.51 (PDF p.54)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_Supplement_DoublingDimLE
import Definitions.Def_ARTreeCover_Supplement_HighwayDimLE
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 42**, p.51 (PDF p.54). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G be a connected n-vertex graph, let k ≥ 1 be an integer parameter, and let ∆, ϵ > 0 and
1 ≤ q ≤ ∞ be real parameters.
1. If G has doubling dimension at most d, it admits an almost-Ramsey embedding
f : V → ℓ_q^{O(log n)} for scale ∆, that satisfy Ω(n/log n · d^{−1/k}) vertices with stretch O(k).
2. If G has (1 + ϵ)-highway dimension at most h(ϵ), it admits an almost-Ramsey embedding
f : V → ℓ_q^{O(log n)} for scale ∆, that satisfy Ω(n/h(ϵ)²) vertices with stretch O(1/ϵ). It also
admits an almost-Ramsey embedding f : V → ℓ_q^{O(log n)} for scale ∆, that satisfy
Ω(n/log n · h(ϵ)^{−1/k}) vertices with stretch O(k)."

**Formalization Note.**
1. `O(x)` is `C · x` and `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other
   parameter. `L(n) = max(1, log₂ n)`; `d`, `h` are clamped to `max(1, ·)`.
2. `ℓ_q^{O(log n)}` is `PiLp q (fun _ : Fin D => ℝ)` with `D ≤ C · L(n)`, for every
   `q ∈ [1, ∞]` (`q : ℝ≥0∞` with `Fact (1 ≤ q)`, `q = ∞` the sup norm); the dimension bound is part of
   the conclusion and uniform in `q`.
3. Correction: the first clause of item 2 (stretch `O(1/ϵ)`) is stated for `ϵ ≤ 1`, the range of
   Theorem 23 it rests on; for large `ϵ` a noncontracting embedding cannot have distortion
   `C/ϵ < 1` on a pair at distance `∆`. The other clauses hold for every `ϵ > 0`.
4. The highway hypothesis is Definition 9 at this `ϵ` with `h = h(ϵ) ∈ ℕ`. -/
theorem theorem_42 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (k : ℕ) (Δ ε : ℝ),
        1 ≤ k → 0 < Δ → 0 < ε → G.graph.Connected →
        (∀ d : ℝ, DoublingDimLE G d →
          (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
              ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * logL (Fintype.card V)) * (max 1 d) ^ (-((1 : ℝ) / k))) (C * k))) ∧
        (∀ h : ℕ, HighwayDimLE G ε h →
          (ε ≤ 1 →
            (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
                ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * (max 1 (h : ℝ)) ^ 2)) (C / ε))) ∧
          (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
              ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * logL (Fintype.card V)) * (max 1 (h : ℝ)) ^ (-((1 : ℝ) / k))) (C * k))) := by sorry

end ARTreeCover.Supplement
