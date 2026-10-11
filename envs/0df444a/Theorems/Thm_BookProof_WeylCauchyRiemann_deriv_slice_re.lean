-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_deriv_slice_re
-- name    : BookProof.WeylCauchyRiemann.deriv_slice_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:34:50.515979+00:00
-- url     : https://prove2.me/theorems/e42c37b2-6280-4957-ad24-be039a18c343
-- title:
--   `BookProof.WeylCauchyRiemann.deriv_slice_re` {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) : deriv (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) x = fderiv ℝ ψ ((x : ℂ) + y...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.deriv_slice_re` {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) : deriv (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) x = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.deriv_slice_re`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.deriv_slice_re
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.deriv_slice_re {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x y : ℝ) :
    deriv (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) x
      = fderiv ℝ ψ ((x : ℂ) + y * Complex.I) 1 := by sorry
