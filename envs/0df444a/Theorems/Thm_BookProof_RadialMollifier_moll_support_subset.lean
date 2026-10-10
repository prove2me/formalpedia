-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_support_subset
-- name    : BookProof.RadialMollifier.moll_support_subset
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:29.107377+00:00
-- url     : https://prove2.me/theorems/16df7564-6fdd-49bf-a196-3a0a0c9244ce
-- title:
--   `BookProof.RadialMollifier.moll_support_subset` {δ : ℝ} (hδ : 0 < δ) : Function.support (moll δ) ⊆ ball (0 : ℂ) δ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_support_subset` {δ : ℝ} (hδ : 0 < δ) : Function.support (moll δ) ⊆ ball (0 : ℂ) δ
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_support_subset`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_support_subset
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_support_subset {δ : ℝ} (hδ : 0 < δ) :
    Function.support (moll δ) ⊆ ball (0 : ℂ) δ := by sorry
