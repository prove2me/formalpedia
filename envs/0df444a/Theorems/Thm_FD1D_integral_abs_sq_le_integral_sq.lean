-- Prove2me | Theorems.Thm_FD1D_integral_abs_sq_le_integral_sq
-- name    : FD1D.integral_abs_sq_le_integral_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:32.051106+00:00
-- url     : https://prove2.me/theorems/317cb967-086d-407f-bf20-f00541567dd0
-- title:
--   FD1 D: integral abs sq le integral sq
-- statement:
--   Cauchy--Schwarz on the unit interval, proved by Jensen for `x ↦ x²`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1744-L1759
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1744-L1759

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.integral_abs_sq_le_integral_sq {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1))
    (hfsq : IntegrableOn (fun z => f z ^ 2) (Icc 0 1)) :
    cdfTransportArea f ^ 2 ≤ ∫ z in Icc (0 : ℝ) 1, f z ^ 2 := by sorry
