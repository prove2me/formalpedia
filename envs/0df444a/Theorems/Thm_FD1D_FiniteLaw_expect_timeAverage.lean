-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_timeAverage
-- name    : FD1D.FiniteLaw.expect_timeAverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:26.390595+00:00
-- url     : https://prove2.me/theorems/055cb37d-babb-56ca-9a55-573232997dc2
-- title:
--   Finite Law: expect time Average
-- statement:
--   Expectation under the time/state mixture is the average expectation.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L42-L61
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L42-L61

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_timeAverage {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (f : Fin T × α → ℝ) :
    (timeAverage hT μ).expect f =
      (∑ t : Fin T, (μ t).expect (fun x => f (t, x))) / (T : ℝ) := by sorry
