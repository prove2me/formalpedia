-- Prove2me | Theorems.Thm_BassokSubstitution_no_stockout_monotone
-- name    : BassokSubstitution.no_stockout_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:41:18.414232+00:00
-- url     : https://prove2.me/theorems/632e380a-d362-4c8f-b8c4-a3bea3f676fe
-- title:
--   Lemma 2 — the no-stock-out probability is nondecreasing in the stock $y_i$
-- statement:
--   Consider the model with Assumptions 1–3, $b \ge 0$, independent nonnegative demands with densities and finite means, and stock levels $y \ge 0$. For classes $k < i$, the quantity
--   $$\Pr\{S^i_i = 0\} + \sum_{m=k}^{i-1} \Pr\{S^{m+1}_i > 0,\ \vec S^m_{m,i} = 0\},$$
--   regarded as a function of the stock $y_i$ of product $i$ (all other stocks fixed), is nondecreasing on $[0, \infty)$.
--
--   In the paper's words: as the stock of product $i$ increases, the probability of no stock-out of class $i$ in the subproblem with products $k, \dots, i$ cannot decrease.
--
--   **Formalization Note.** The paper states $\frac{\partial}{\partial y_i}\{\cdots\} \ge 0$. With `deriv`, a non-differentiable point would make this trivially true, so the monotone form is stated instead; it implies the derivative inequality wherever the derivative exists. The paper leaves $k$ implicit; it is Lemma 1's $k < i$. The sum's general term is as in Lemma 1. Indices are 0-based in Lean.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, Lemma 2

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Lemma 2 (monotone form): for classes `k < i` (0-based), the left-hand side of Lemma 1 is a
nondecreasing function of the stock `y_i` of product `i` on `[0, ∞)`, the other stocks being
fixed. -/
theorem no_stockout_monotone {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (y : Fin N → ℝ) (hy : 0 ≤ y) (k i : Fin N) (hki : k < i) :
    MonotoneOn
      (fun t : ℝ =>
        (Measure.pi ν).real {d | shortage (Function.update y i t) d i i = 0}
          + ∑ m ∈ Finset.univ.filter (fun m : Fin N => k ≤ m ∧ m < i),
              (Measure.pi ν).real {d | 0 < shortage (Function.update y i t) d (m + 1) i ∧
                ShortVecZero (Function.update y i t) d m m i})
      (Set.Ici 0) := by sorry

end BassokSubstitution
