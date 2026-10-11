-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_tendsto
-- name    : BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:44.056434+00:00
-- url     : https://prove2.me/theorems/65102557-0b97-4a8e-a94c-d748738d6234
-- title:
--   `BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto` : Tendsto (fun n => (bumpSeq n).rOut) atTop (nhds 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto` : Tendsto (fun n => (bumpSeq n).rOut) atTop (nhds 0)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.bumpSeq_rOut_tendsto : Tendsto (fun n => (bumpSeq n).rOut) atTop (nhds 0) := by sorry
