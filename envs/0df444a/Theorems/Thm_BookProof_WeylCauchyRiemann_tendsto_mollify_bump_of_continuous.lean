-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_tendsto_mollify_bump_of_continuous
-- name    : BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:00.1012+00:00
-- url     : https://prove2.me/theorems/cfb293ef-fc9a-411a-812a-49dacede2580
-- title:
--   `BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous` {h : ℂ → ℂ} (hh : Continuous h) (z : ℂ) : Tendsto (fun n => mollify h ((bumpSeq n).normed volume) z) atTop (nhds (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous` {h : ℂ → ℂ} (hh : Continuous h) (z : ℂ) : Tendsto (fun n => mollify h ((bumpSeq n).normed volume) z) atTop (nhds (h z))
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.tendsto_mollify_bump_of_continuous {h : ℂ → ℂ} (hh : Continuous h) (z : ℂ) :
    Tendsto (fun n => mollify h ((bumpSeq n).normed volume) z) atTop (nhds (h z)) := by sorry
