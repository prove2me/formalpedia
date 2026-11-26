-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_sq_le_expect_sq
-- name    : FD1D.FiniteLaw.expect_sq_le_expect_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:15.545935+00:00
-- url     : https://prove2.me/theorems/03065e71-33bc-5887-bcb1-1dd28f8adc8b
-- title:
--   Finite Law: expect sq le expect sq
-- statement:
--   Weighted Cauchy--Schwarz for the project's finite-law expectation.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1777-L1802
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1777-L1802

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.FiniteLaw

theorem FD1D.FiniteLaw.expect_sq_le_expect_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by sorry
