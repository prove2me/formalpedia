-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_scalar_exponential_deficit_right_slope
-- name    : AvramDividend.Classical.avram_wave5_04c_scalar_exponential_deficit_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:52:03.552256+00:00
-- url     : https://prove2.me/theorems/9d296bd8-c29f-48ba-b6ac-4d583176b6ce
-- title:
--   Exact right derivative of scalar exponential deficit
-- statement:
--   For each real A, the right-hand real-neighborhood limit of h^{-1}(1-exp(-h*A)) is exactly A. The complete formal proof uses HasDerivAt of a real linear map composed with exponential, the punctured-neighborhood slope characterisation, restriction to Ioi 0, and a final sign algebra identity. This supplies the deterministic calculus step to transfer the already Proved original-process BV drift-residual Laplace transform into an exact small-time exponential generator slope.
-- source:
--   Remote compiler sentinel-verified complete Lean source candidates/work_on/AvramDividend_04c_scalar_exp_deficit_right_slope_probe.lean

import Mathlib
set_option autoImplicit false
open Filter Set

theorem AvramDividend.Classical.avram_wave5_04c_scalar_exponential_deficit_right_slope (A : ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ * (1 - Real.exp (-(h * A))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds A) := by sorry
