-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_timeAverage_eq_sum_range
-- name    : FD1D.FiniteLaw.expect_timeAverage_eq_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:32.620803+00:00
-- url     : https://prove2.me/theorems/87727816-7567-5275-943d-e1b737099745
-- title:
--   Finite Law: expect time Average eq sum range
-- statement:
--   Range-indexed form of `expect_timeAverage`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L64-L72
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L64-L72

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_timeAverage_eq_sum_range {T : ℕ} (hT : 0 < T)
    (μ : ℕ → FiniteLaw α) (f : ℕ → α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.1 z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect (f t)) / (T : ℝ) := by sorry
