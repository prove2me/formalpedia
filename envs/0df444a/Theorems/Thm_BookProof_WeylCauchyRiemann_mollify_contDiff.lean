-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_contDiff
-- name    : BookProof.WeylCauchyRiemann.mollify_contDiff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:57.661912+00:00
-- url     : https://prove2.me/theorems/ed40d0d8-f1d0-47dc-9a76-c2ee85cafe3f
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_contDiff` {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : ContDiff ℝ ∞...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_contDiff` {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : ContDiff ℝ ∞ (mollify F χ)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_contDiff`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_contDiff
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_contDiff {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (mollify F χ) := by sorry
