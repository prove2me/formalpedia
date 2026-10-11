-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_comm
-- name    : BookProof.WeylCauchyRiemann.mollify_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:57.298765+00:00
-- url     : https://prove2.me/theorems/1a5e701c-1e82-4480-96a2-031cd6bdb3ae
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_comm` {F : ℂ → ℂ} (hF : Integrable F) {χ₁ χ₂ : ℂ → ℝ} (hχ₁ : Continuous χ₁) (hχ₁c : HasCompactSupport χ₁) (hχ₂ : Continuous...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_comm` {F : ℂ → ℂ} (hF : Integrable F) {χ₁ χ₂ : ℂ → ℝ} (hχ₁ : Continuous χ₁) (hχ₁c : HasCompactSupport χ₁) (hχ₂ : Continuous χ₂) (hχ₂c : HasCompactSupport χ₂) : mollify (mollify F χ₁) χ₂ = mollify (mollify F χ₂) χ₁
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_comm`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_comm
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_comm {F : ℂ → ℂ} (hF : Integrable F) {χ₁ χ₂ : ℂ → ℝ}
    (hχ₁ : Continuous χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : Continuous χ₂) (hχ₂c : HasCompactSupport χ₂) :
    mollify (mollify F χ₁) χ₂ = mollify (mollify F χ₂) χ₁ := by sorry
