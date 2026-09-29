-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_evalHorner
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:03:00.349613+00:00
-- url     : https://prove2.me/theorems/039901b3-7670-4a30-900b-be9a44d4252e
-- title:
--   The interval evaluator is inclusion-isotone**: the exact value at any point of the input interval is enclosed by the interval evaluation
-- statement:
--   **The interval evaluator is inclusion-isotone**: the exact value at any point of
--   the input interval is enclosed by the interval evaluation.  This is the property that
--   turns a computed enclosure into a rigorous bound over the whole box.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 474–483.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L474-L483

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner : ∀ (cs : List ℝ) (I : CertInterval) (x : ℝ), I.Mem x →
    (evalHorner cs I).Mem (polyEval cs x) := by sorry
