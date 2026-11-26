-- Prove2me | Theorems.Thm_FD1D_expected_area_le_sqrt_l2
-- name    : FD1D.expected_area_le_sqrt_l2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:33.139718+00:00
-- url     : https://prove2.me/theorems/c9e48726-7dc7-4925-ba06-a98fa4187eef
-- title:
--   FD1 D: expected area le sqrt l2
-- statement:
--   CDF-area transport followed by Cauchy--Schwarz in space and in state.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1819-L1826
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1819-L1826

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.expected_area_le_sqrt_l2 (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i) :
    μ.expect (fun ω => cdfTransportArea (haarCombination l p (b ω))) ≤
      Real.sqrt (μ.expect (fun ω => haarL2 l p (b ω))) := by sorry
