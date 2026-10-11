-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_ae_tendsto_mollify_bump
-- name    : BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:15:17.078688+00:00
-- url     : https://prove2.me/theorems/35c7f3b4-8aa8-4714-b70b-cb291e4c3113
-- title:
--   `BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump` {F : ℂ → ℂ} (hF : LocallyIntegrable F) : ∀ᵐ z : ℂ, Tendsto (fun n => mollify F ((bumpSeq n).normed volume) z) atTop (nhds (F z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump` {F : ℂ → ℂ} (hF : LocallyIntegrable F) : ∀ᵐ z : ℂ, Tendsto (fun n => mollify F ((bumpSeq n).normed volume) z) atTop (nhds (F z))
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.ae_tendsto_mollify_bump {F : ℂ → ℂ} (hF : LocallyIntegrable F) :
    ∀ᵐ z : ℂ, Tendsto (fun n => mollify F ((bumpSeq n).normed volume) z) atTop (nhds (F z)) := by sorry
