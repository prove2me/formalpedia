-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_integral_fderiv_I_eq_zero
-- name    : BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:16.957651+00:00
-- url     : https://prove2.me/theorems/2923d5d0-3357-4201-b81b-e335da655957
-- title:
--   `BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero` {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z Complex.I = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero` {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z Complex.I = 0
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.integral_fderiv_I_eq_zero {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : ∫ z : ℂ, fderiv ℝ ψ z Complex.I = 0 := by sorry
