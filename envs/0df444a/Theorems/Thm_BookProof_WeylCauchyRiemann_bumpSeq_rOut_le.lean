-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_rOut_le
-- name    : BookProof.WeylCauchyRiemann.bumpSeq_rOut_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:40.708004+00:00
-- url     : https://prove2.me/theorems/7947cf6f-dae6-4804-95bf-a616af4f8b9f
-- title:
--   `BookProof.WeylCauchyRiemann.bumpSeq_rOut_le` (n : ℕ) : (bumpSeq n).rOut ≤ 2 * (bumpSeq n).rIn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.bumpSeq_rOut_le` (n : ℕ) : (bumpSeq n).rOut ≤ 2 * (bumpSeq n).rIn
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.bumpSeq_rOut_le`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.bumpSeq_rOut_le
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.bumpSeq_rOut_le (n : ℕ) : (bumpSeq n).rOut ≤ 2 * (bumpSeq n).rIn := by sorry
