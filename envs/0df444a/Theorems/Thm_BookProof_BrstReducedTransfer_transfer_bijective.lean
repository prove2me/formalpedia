-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_transfer_bijective
-- name    : BookProof.BrstReducedTransfer.transfer_bijective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:11:01.670646+00:00
-- url     : https://prove2.me/theorems/2804f0dd-51d6-4eb6-b94b-bb0b817f86c1
-- title:
--   `BookProof.BrstReducedTransfer.transfer_bijective` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (t : ℝ) : Function.Bijective (transfer Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.transfer_bijective` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (t : ℝ) : Function.Bijective (transfer Om U hcomm t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.transfer_bijective`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.transfer_bijective
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

theorem BookProof.BrstReducedTransfer.transfer_bijective (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (t : ℝ) :
    Function.Bijective (transfer Om U hcomm t) := by sorry
