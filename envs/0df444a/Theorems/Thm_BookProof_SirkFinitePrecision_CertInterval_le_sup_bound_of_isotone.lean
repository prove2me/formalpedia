-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_le_sup_bound_of_isotone
-- name    : BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:43:12.305203+00:00
-- url     : https://prove2.me/theorems/7a1dfa1d-e9e1-40ea-b53c-cb261e088078
-- title:
--   The certified supremum (Layer 2, §4.2).** An interval evaluator that encloses `f` on every point of the box gives a rigorous upper bound for `f` on the whole box — unlike the grid maximum
-- statement:
--   **The certified supremum (Layer 2, §4.2).**  An interval evaluator that encloses
--   `f` on every point of the box gives a rigorous upper bound for `f` on the whole box —
--   unlike the grid maximum computed by the code, which is only a lower bound for the
--   supremum.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 451–457.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L451-L457

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone {α : Type*} (f : α → ℝ) (S : Set α) (I : CertInterval)
    (hF : ∀ z ∈ S, I.Mem (f z)) {z : α} (hz : z ∈ S) :
    f z ≤ I.hi := by sorry
