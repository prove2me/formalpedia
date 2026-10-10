-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_eq_zero_of_le
-- name    : BookProof.RadialMollifier.moll_eq_zero_of_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:30.444568+00:00
-- url     : https://prove2.me/theorems/ff81d977-5faf-4163-8d43-8b8647043279
-- title:
--   `BookProof.RadialMollifier.moll_eq_zero_of_le` {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : δ ≤ ‖z‖) : moll δ z = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_eq_zero_of_le` {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : δ ≤ ‖z‖) : moll δ z = 0
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_eq_zero_of_le`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_eq_zero_of_le
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_eq_zero_of_le {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (h : δ ≤ ‖z‖) : moll δ z = 0 := by sorry
