-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_right
-- name    : BookProof.WeylCauchyRiemann.mollify_eq_convolution_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:28.531776+00:00
-- url     : https://prove2.me/theorems/beb61788-74f9-4457-aa65-b3ddb74e4749
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_eq_convolution_right` (F : ℂ → ℂ) (χ : ℂ → ℝ) : mollify F χ = F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] χ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_eq_convolution_right` (F : ℂ → ℂ) (χ : ℂ → ℝ) : mollify F χ = F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] χ
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_eq_convolution_right`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_eq_convolution_right
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_eq_convolution_right (F : ℂ → ℂ) (χ : ℂ → ℝ) :
    mollify F χ = F ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] χ := by sorry
