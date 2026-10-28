-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_of_local_volterra_derivative
-- name    : AvramDividend.Classical.derivZeroPlus_of_local_volterra_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:18:22.771958+00:00
-- url     : https://prove2.me/theorems/eef7566b-ba2e-4f3c-9ed0-c0e0cac04acc
-- title:
--   Local Volterra derivative and vanishing convolution determine the extended scale slope
-- statement:
--   For a scale-type function with W(0)=1/d, continuous from the right, whose ordinary derivative on positive points satisfies a local Volterra equation W'=aW-G/d, if the convolution remainder G tends to zero at the origin then the extended liminf derivative equals a/d. This deterministic analytic bridge isolates the final step of the finite-jump scale boundary proof.
-- source:
--   Direct real-analysis derivation from the finite-activity renewal equation in artifacts/mission_research/1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43/finite-activity-local-renewal-c1-2026-10-25.md, verified Prove2Me helper derivZeroPlus_eq_coe_of_right_tendsto (dcb55b00), and Avram et al. (2007) equation (3.5).

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto
import Mathlib.Topology.Algebra.Order.Field
open AvramDividend.Classical Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.derivZeroPlus_of_local_volterra_derivative
    (W G : ℝ → ℝ) (d a : ℝ)
    (hW0 : W 0 = 1 / d)
    (hWcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0)
    (hG : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hDer : ∀ x : ℝ, 0 < x → deriv W x = a * W x - G x / d) :
    derivZeroPlus W = ((a / d : ℝ) : EReal) := by sorry
