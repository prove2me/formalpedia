-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_continuous
-- name    : BookProof.RadialMollifier.moll_continuous
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:00:45.621481+00:00
-- url     : https://prove2.me/theorems/a5c38377-2572-40be-92a1-90f0ec41f6cf
-- title:
--   `BookProof.RadialMollifier.moll_continuous` (δ : ℝ) : Continuous (moll δ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_continuous` (δ : ℝ) : Continuous (moll δ)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_continuous`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_continuous
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_continuous (δ : ℝ) : Continuous (moll δ) := by sorry
