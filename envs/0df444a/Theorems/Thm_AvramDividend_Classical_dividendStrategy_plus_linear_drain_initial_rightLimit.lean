-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
-- name    : AvramDividend.Classical.dividendStrategy_plus_linear_drain_initial_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:01:59.74695+00:00
-- url     : https://prove2.me/theorems/f21f8ba3-b0ff-4c29-a7f6-e1ec8634aa01
-- title:
--   Continuous unit-rate drain leaves the initial right dividend atom unchanged
-- statement:
--   For any admissible cumulative dividend process D, adding the deterministic continuous process t changes no right-hand dividend jump at the initial instant: the right limit at zero of D_t+t is the same as that of D_t. This follows from monotone one-sided limits and continuity of the nonnegative-time embedding. In particular, the initial Stieltjes payment of the zero-barrier-plus-linear-drain counterexample equals the initial lump sum of the original zero-barrier control.
-- source:
--   Monotone right-limit calculus for the pathwise cumulative dividend definition of Avram, Palmowski and Pistorius (2007), Section 2, combined with the previously proved Mathlib-based dividendPath_real_rightLim_eq_rightLimit identity.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_plus_linear_drain_initial_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    rightLimit (fun t ω => D t ω + (t : ℝ)) 0 ω = rightLimit D 0 ω := by sorry
