-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_neg
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:45:38.483891+00:00
-- url     : https://prove2.me/theorems/aa0ea5f4-77bc-4285-91bd-c0ca19a84eb7
-- title:
--   Interval negation is sound for membership
-- statement:
--   Interval negation is sound for membership.
--
--   If $x$ lies in the interval $I$ then $-x$ lies in the negated interval:
--   $$
--   I\ni x \;\Longrightarrow\; (-I)\ni(-x).
--   $$
--
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_neg` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 402–403.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L402-L403

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_neg
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_neg {I : CertInterval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by sorry
