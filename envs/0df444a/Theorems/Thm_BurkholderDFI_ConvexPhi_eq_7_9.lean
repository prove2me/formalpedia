-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_7_9
-- name    : BurkholderDFI.ConvexPhi.eq_7_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:16.441982+00:00
-- url     : https://prove2.me/theorems/6deca058-8315-4574-9804-f62f83187851
-- title:
--   (7.9) — quasi-subadditivity of Φ
-- statement:
--   For a nondecreasing function $\Phi$ satisfying the moderate-growth bound $\Phi(2x)\le c\Phi(x)$ and any $x,y\ge0$,
--   $$
--   \Phi(x+y)\le\Phi(2x)+\Phi(2y)\le c[\Phi(x)+\Phi(y)].
--   $$
--   This is the sum estimate used in the convex-function comparison.
--
--   **Formalization Note** All arguments and values may be infinite; the same growth constant $c$ appears in the second inequality.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (7.9), p. 27

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (7.9), p. 27: quasi-subadditivity from the growth condition. -/
theorem eq_7_9 (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (x y : ℝ≥0∞) :
    Φ (x + y) ≤ Φ (2 * x) + Φ (2 * y) ∧
    Φ (2 * x) + Φ (2 * y) ≤ c * (Φ x + Φ y) := by sorry
end BurkholderDFI.ConvexPhi
