-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_dist_le_width
-- name    : BookProof.SirkFinitePrecision.CertInterval.dist_le_width
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:42:25.721225+00:00
-- url     : https://prove2.me/theorems/662ec2c4-3919-4de6-9f46-51f1e4be72bf
-- title:
--   The certified half-width.** If both the exact value and the delivered value are enclosed by the same interval, they differ by at most its width — this is the `h_O` term of the §4.4 assembl
-- statement:
--   **The certified half-width.**  If both the exact value and the delivered value are
--   enclosed by the same interval, they differ by at most its width — this is the `h_O`
--   term of the §4.4 assembled width.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.dist_le_width` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 442–449.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L442-L449

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.dist_le_width
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.dist_le_width {I : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : I.Mem y) :
    |x - y| ≤ I.width := by sorry
