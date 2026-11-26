-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_le_sqrt_expect_sq
-- name    : FD1D.FiniteLaw.expect_le_sqrt_expect_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:38.867258+00:00
-- url     : https://prove2.me/theorems/95756c0d-9194-4a4e-8f29-1d30f4fddcb4
-- title:
--   Finite Law: expect le sqrt expect sq
-- statement:
--   The Finite Law construction uses the expect le sqrt expect sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1804-L1814
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1804-L1814

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.FiniteLaw

theorem FD1D.FiniteLaw.expect_le_sqrt_expect_sq (μ : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ^ 2 ≤ g ω) :
    μ.expect f ≤ Real.sqrt (μ.expect g) := by sorry
