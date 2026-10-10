-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_polarSymm_eq
-- name    : BookProof.RadialMollifier.polarSymm_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:02:31.605893+00:00
-- url     : https://prove2.me/theorems/83ffee49-43d6-40d8-b1fe-822259947f27
-- title:
--   `BookProof.RadialMollifier.polarSymm_eq` (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.polarSymm_eq` (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.polarSymm_eq`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.polarSymm_eq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.polarSymm_eq (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by sorry
