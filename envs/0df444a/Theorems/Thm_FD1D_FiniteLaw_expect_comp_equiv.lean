-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_comp_equiv
-- name    : FD1D.FiniteLaw.expect_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:55.504404+00:00
-- url     : https://prove2.me/theorems/d88e7f15-64e4-4c1a-902d-0561c880011c
-- title:
--   Finite Law: expect comp equiv
-- statement:
--   The Finite Law construction uses the expect comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1052-L1062
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1052-L1062

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem FD1D.FiniteLaw.expect_comp_equiv (μ : FiniteLaw Ω) (e : Ω ≃ Ω)
    (he : InvariantUnder μ e) (f : Ω → ℝ) :
    μ.expect (fun ω => f (e ω)) = μ.expect f := by sorry
