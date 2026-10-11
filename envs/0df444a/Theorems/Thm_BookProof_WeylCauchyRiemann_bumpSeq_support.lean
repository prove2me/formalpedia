-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_support
-- name    : BookProof.WeylCauchyRiemann.bumpSeq_support
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:16:04.248788+00:00
-- url     : https://prove2.me/theorems/38865530-d6bd-4771-a88e-568e309a8ad6
-- title:
--   `BookProof.WeylCauchyRiemann.bumpSeq_support` (n : ℕ) : Function.support ((bumpSeq n).normed volume) ⊆ ball (0 : ℂ) ((bumpSeq n).rOut)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.bumpSeq_support` (n : ℕ) : Function.support ((bumpSeq n).normed volume) ⊆ ball (0 : ℂ) ((bumpSeq n).rOut)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.bumpSeq_support`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.bumpSeq_support
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.bumpSeq_support (n : ℕ) :
    Function.support ((bumpSeq n).normed volume) ⊆ ball (0 : ℂ) ((bumpSeq n).rOut) := by sorry
