-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_polyEval_le_of_mem
-- name    : BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:12:21.646708+00:00
-- url     : https://prove2.me/theorems/71b97929-6b43-4c8b-85df-f08a4a9cdee5
-- title:
--   The certified supremum of a polynomial over a box, from one interval evaluation: no grid, no sampling
-- statement:
--   The certified supremum of a polynomial over a box, from one interval evaluation:
--   no grid, no sampling.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 485–488.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L485-L488

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    polyEval cs x ≤ (evalHorner cs I).hi := by sorry
