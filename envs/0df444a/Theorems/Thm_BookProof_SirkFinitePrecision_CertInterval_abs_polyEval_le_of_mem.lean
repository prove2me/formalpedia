-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_abs_polyEval_le_of_mem
-- name    : BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:11:36.123526+00:00
-- url     : https://prove2.me/theorems/212c5576-54c4-4012-93df-eb9a70932887
-- title:
--   The two-sided version: a certified bound `R_cert ≥ sup |p|` over the box
-- statement:
--   The two-sided version: a certified bound `R_cert ≥ sup |p|` over the box.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 490–503.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L490-L503

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    |polyEval cs x| ≤ max |(evalHorner cs I).lo| |(evalHorner cs I).hi| := by sorry
