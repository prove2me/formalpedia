-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_contDiff_normSq
-- name    : BookProof.RadialMollifier.contDiff_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:59.727495+00:00
-- url     : https://prove2.me/theorems/78282b5d-832f-43b9-955c-0afd8c8b36ec
-- title:
--   `BookProof.RadialMollifier.contDiff_normSq` : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.contDiff_normSq` : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.contDiff_normSq`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.contDiff_normSq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.contDiff_normSq : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by sorry
