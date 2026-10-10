-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_hasCompactSupport
-- name    : BookProof.RadialMollifier.moll_hasCompactSupport
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:44.000925+00:00
-- url     : https://prove2.me/theorems/fed79736-7baa-48c8-a99e-bfab75a92617
-- title:
--   `BookProof.RadialMollifier.moll_hasCompactSupport` {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (moll δ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_hasCompactSupport` {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (moll δ)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_hasCompactSupport`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (moll δ) := by sorry
