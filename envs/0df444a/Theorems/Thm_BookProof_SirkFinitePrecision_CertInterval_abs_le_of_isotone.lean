-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_abs_le_of_isotone
-- name    : BookProof.SirkFinitePrecision.CertInterval.abs_le_of_isotone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:41:46.512693+00:00
-- url     : https://prove2.me/theorems/845824b8-c04e-4d7b-be9a-cb62ead550e8
-- title:
--   The two-sided form, `‖f − p/q‖_{∞,Σ} ≤ R_cert`
-- statement:
--   The two-sided form, `‖f − p/q‖_{∞,Σ} ≤ R_cert`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.abs_le_of_isotone` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 505–513.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L505-L513

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.abs_le_of_isotone
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.abs_le_of_isotone {α : Type*} (f : α → ℝ) (S : Set α) (I : CertInterval)
    (hF : ∀ z ∈ S, I.Mem (f z)) (R : ℝ) (hR : max |I.lo| |I.hi| ≤ R) {z : α} (hz : z ∈ S) :
    |f z| ≤ R := by sorry
