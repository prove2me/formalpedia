-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_mollify
-- name    : BookProof.WeylCauchyRiemann.dbar_mollify
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:44.683179+00:00
-- url     : https://prove2.me/theorems/adc385a0-db4d-4908-89c8-f893ed5d5a17
-- title:
--   `BookProof.WeylCauchyRiemann.dbar_mollify` {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (z : ℂ) : dbar (mollify F...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.dbar_mollify` {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (z : ℂ) : dbar (mollify F χ) z = ∫ w : ℂ, dbarR χ (z - w) * F w
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.dbar_mollify`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.dbar_mollify
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.dbar_mollify {F : ℂ → ℂ} (hF : LocallyIntegrable F) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (z : ℂ) :
    dbar (mollify F χ) z = ∫ w : ℂ, dbarR χ (z - w) * F w := by sorry
