-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_mul
-- name    : BookProof.SirkFinitePrecision.CertInterval.mem_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:44:55.556112+00:00
-- url     : https://prove2.me/theorems/47368f43-3979-4d67-bc67-8e6ed8ef8054
-- title:
--   Interval multiplication is sound for membership
-- statement:
--   Interval multiplication is sound for membership.
--
--   If $x$ lies in $I$ and $y$ lies in $J$ then their product lies in the interval product: $I.\text{mul}(J) \ni (x\,y)$. The product interval is built from all four endpoint products, so the soundness proof checks each pairing.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.CertInterval.mem_mul` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 421–428.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L421-L428

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.CertInterval.mem_mul
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.CertInterval.mem_mul {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by sorry
