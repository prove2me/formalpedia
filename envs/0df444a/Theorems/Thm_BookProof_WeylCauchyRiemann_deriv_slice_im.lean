-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_deriv_slice_im
-- name    : BookProof.WeylCauchyRiemann.deriv_slice_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:34:11.767544+00:00
-- url     : https://prove2.me/theorems/a1949691-ee89-4bdd-8f3b-8b73b381a94f
-- title:
--   `BookProof.WeylCauchyRiemann.deriv_slice_im` {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) : deriv (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) y = fderiv ℝ ψ ((x : ℂ) + y...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.deriv_slice_im` {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) : deriv (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) y = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) Complex.I
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.deriv_slice_im`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.deriv_slice_im
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.deriv_slice_im {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) :
    deriv (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) y
      = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) Complex.I := by sorry
