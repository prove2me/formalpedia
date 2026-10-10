-- Prove2me | Theorems.Thm_BookProof_RadialMollifier_moll_integrable
-- name    : BookProof.RadialMollifier.moll_integrable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:01:30.4744+00:00
-- url     : https://prove2.me/theorems/d51f3907-a613-47d3-a28b-010b9d141a7a
-- title:
--   `BookProof.RadialMollifier.moll_integrable` {δ : ℝ} (hδ : 0 < δ) : Integrable (moll δ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialMollifier`.
--
--   `BookProof.RadialMollifier.moll_integrable` {δ : ℝ} (hδ : 0 < δ) : Integrable (moll δ)
--
--   Formalization note: Lean 4 identifier `BookProof.RadialMollifier.moll_integrable`.

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.moll_integrable
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

theorem BookProof.RadialMollifier.moll_integrable {δ : ℝ} (hδ : 0 < δ) : Integrable (moll δ) := by sorry
