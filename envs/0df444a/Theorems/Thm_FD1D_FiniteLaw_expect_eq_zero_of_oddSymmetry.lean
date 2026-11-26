-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_eq_zero_of_oddSymmetry
-- name    : FD1D.FiniteLaw.expect_eq_zero_of_oddSymmetry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:43.414111+00:00
-- url     : https://prove2.me/theorems/c45ac156-fe27-43b8-b58a-8e48ce7191cb
-- title:
--   Finite Law: expect eq zero of odd Symmetry
-- statement:
--   A mass-preserving sign flip forces expectation zero.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1065-L1076
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1065-L1076

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem FD1D.FiniteLaw.expect_eq_zero_of_oddSymmetry (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hodd : OddSymmetry μ f) :
    μ.expect f = 0 := by sorry
