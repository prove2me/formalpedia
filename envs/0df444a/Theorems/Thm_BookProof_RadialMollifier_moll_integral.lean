-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_integral
-- name    : BookProof.RadialMollifier.moll_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:56.176104+00:00
-- url     : https://prove2.me/theorems/b268adaa-1dee-42a4-9200-bb6e4908a5b0
-- title:
--   `BookProof.RadialMollifier.moll_integral` {δ : ℝ} (hδ : 0 < δ) : ∫ z : ℂ, moll δ z = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_integral` {δ : ℝ} (hδ : 0 < δ) : ∫ z : ℂ, moll δ z = 1
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_integral`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_integral
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_integral {δ : ℝ} (hδ : 0 < δ) : ∫ z : ℂ, moll δ z = 1 := by sorry
