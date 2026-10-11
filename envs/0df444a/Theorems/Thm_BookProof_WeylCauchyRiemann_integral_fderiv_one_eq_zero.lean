-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_integral_fderiv_one_eq_zero
-- name    : BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:39.473473+00:00
-- url     : https://prove2.me/theorems/8c898e4f-2aba-4175-ad3b-6c622eb047f0
-- title:
--   `BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero` {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z 1 = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero` {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z 1 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.integral_fderiv_one_eq_zero {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z 1 = 0 := by sorry
