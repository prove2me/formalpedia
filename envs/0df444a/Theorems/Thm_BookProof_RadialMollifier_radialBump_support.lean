-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_radialBump_support
-- name    : BookProof.RadialMollifier.radialBump_support
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:00:22.411648+00:00
-- url     : https://prove2.me/theorems/aaf00b56-ed82-47da-822f-a589c62243f0
-- title:
--   `BookProof.RadialMollifier.radialBump_support` : Function.support radialBump = ball (0 : ℂ) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.radialBump_support` : Function.support radialBump = ball (0 : ℂ) 1
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.radialBump_support`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.radialBump_support
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.radialBump_support : Function.support radialBump = ball (0 : ℂ) 1 := by sorry
