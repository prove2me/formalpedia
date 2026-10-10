-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_contDiff
-- name    : BookProof.RadialMollifier.moll_contDiff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:22.699979+00:00
-- url     : https://prove2.me/theorems/195310bc-f888-4ce5-8c9e-8de403fe6583
-- title:
--   `BookProof.RadialMollifier.moll_contDiff` (δ : ℝ) : ContDiff ℝ ∞ (moll δ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_contDiff` (δ : ℝ) : ContDiff ℝ ∞ (moll δ)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_contDiff`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_contDiff
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_contDiff (δ : ℝ) : ContDiff ℝ ∞ (moll δ) := by sorry
