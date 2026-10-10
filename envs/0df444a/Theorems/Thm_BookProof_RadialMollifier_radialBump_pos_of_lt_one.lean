-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_radialBump_pos_of_lt_one
-- name    : BookProof.RadialMollifier.radialBump_pos_of_lt_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:59:56.601505+00:00
-- url     : https://prove2.me/theorems/778e8dff-c7df-4332-9a8a-77d944962bd0
-- title:
--   `BookProof.RadialMollifier.radialBump_pos_of_lt_one` {z : ℂ} (h : ‖z‖ < 1) : 0 < radialBump z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.radialBump_pos_of_lt_one` {z : ℂ} (h : ‖z‖ < 1) : 0 < radialBump z
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.radialBump_pos_of_lt_one`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.radialBump_pos_of_lt_one
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.radialBump_pos_of_lt_one {z : ℂ} (h : ‖z‖ < 1) : 0 < radialBump z := by sorry
