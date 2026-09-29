-- Prove2me | Theorems.Thm_BassokSubstitution_salvage_savings_bound
-- name    : BassokSubstitution.salvage_savings_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:49:10.500513+00:00
-- url     : https://prove2.me/theorems/59c5a15e-7332-42ce-a89a-c3e61e247f2f
-- title:
--   Lemma 5 — the salvage-weighted no-stock-out terms grow no faster than $s_1$ times their sum
-- statement:
--   Consider the model with Assumptions 1–3, $b \ge 0$, independent nonnegative demands with densities and finite means, and stock levels $y \ge 0$. For a class $i$ put
--   $$A(y) = s_i \Pr\{S^i_i = 0\} + \sum_{m=1}^{i-1} s_m \Pr\{S^{m+1}_i > 0,\ \vec S^m_{m,i} = 0\},\qquad B(y) = \Pr\{S^i_i = 0\} + \sum_{m=1}^{i-1} \Pr\{S^{m+1}_i > 0,\ \vec S^m_{m,i} = 0\}.$$
--   Then, as a function of the stock $y_i$ of product $i$ on $[0,\infty)$ (all other stocks fixed), $s_1 B - A$ is nondecreasing. In particular, wherever the derivatives exist,
--   $$\frac{\partial A}{\partial y_i} \le s_1 \frac{\partial B}{\partial y_i}.$$
--
--   This is the paper's upper bound on the savings in shortage costs for an additional unit of product $i$ in the subproblem with products $1, \dots, i$; it controls the salvage terms (5d) in the proof of Theorem 2.
--
--   **Formalization Note.** The paper states the derivative inequality; the monotone form is stated instead, since `deriv` would make the inequality trivially true at non-differentiable points, and it implies the derivative form wherever the derivatives exist. The sums' general terms are inferred from the printed first and last terms. $s_1$ is `M.s 0` (0-based indices), and `NeZero N` provides the index `0`.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, Lemma 5

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 5 (monotone form): for a class `i` (0-based), `s_1` times the no-stock-out
probability of Lemma 1 (with `k` the first product) minus the salvage-weighted sum of the same
probabilities is nondecreasing in the stock `y_i` on `[0, ∞)`. -/
theorem salvage_savings_bound {N : ℕ} [NeZero N] (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (i : Fin N) :
    MonotoneOn
      (fun t : ℝ =>
        M.s 0 * ((Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i})
          - (M.s i * (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
            + ∑ m ∈ Finset.univ.filter (fun m : Fin N => m < i),
                M.s m * (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                  ShortVecZero (Function.update y i t) d m m i}))
      (Set.Ici 0) := by sorry

end BassokSubstitution
