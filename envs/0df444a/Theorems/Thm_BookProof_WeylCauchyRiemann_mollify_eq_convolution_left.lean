-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_eq_convolution_left
-- name    : BookProof.WeylCauchyRiemann.mollify_eq_convolution_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:17.469973+00:00
-- url     : https://prove2.me/theorems/d7ad6b8d-7d0c-4798-a8e6-01d69919940c
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_eq_convolution_left` (F : ℂ → ℂ) (χ : ℂ → ℝ) : mollify F χ = χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_eq_convolution_left` (F : ℂ → ℂ) (χ : ℂ → ℝ) : mollify F χ = χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_eq_convolution_left`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_eq_convolution_left
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_eq_convolution_left (F : ℂ → ℂ) (χ : ℂ → ℝ) :
    mollify F χ = χ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F := by sorry
