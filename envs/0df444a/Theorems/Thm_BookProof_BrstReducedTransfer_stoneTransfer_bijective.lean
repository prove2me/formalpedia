-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneTransfer_bijective
-- name    : BookProof.BrstReducedTransfer.stoneTransfer_bijective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:11:34.257973+00:00
-- url     : https://prove2.me/theorems/73603755-87d6-4b75-b8a8-875800fe6998
-- title:
--   `BookProof.BrstReducedTransfer.stoneTransfer_bijective` (t : ℝ) : Function.Bijective (stoneTransfer T Om hcomm t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.stoneTransfer_bijective` (t : ℝ) : Function.Bijective (stoneTransfer T Om hcomm t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.stoneTransfer_bijective`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.stoneTransfer_bijective
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

theorem BookProof.BrstReducedTransfer.stoneTransfer_bijective (t : ℝ) : Function.Bijective (stoneTransfer T Om hcomm t) := by sorry
