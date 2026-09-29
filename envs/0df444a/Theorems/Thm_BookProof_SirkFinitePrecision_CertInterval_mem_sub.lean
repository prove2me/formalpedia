-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_sub
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:47:54.337777+00:00
-- url     : https://prove2.me/theorems/a534affb-d0d4-4484-a81d-dcd99f93c6b6
-- title:
--   Interval subtraction is sound for membership
-- statement:
--   Interval subtraction is sound for membership.
--
--   If $x$ lies in $I$ and $y$ lies in $J$ then $x-y$ lies in the interval difference: $I.\text{sub}(J) \ni (x-y)$.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_sub` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 405–407.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L405-L407

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_sub
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_sub {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x - y) := by sorry
