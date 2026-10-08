-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_inner_block_im_eq_zero
-- name    : BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:32:17.174981+00:00
-- url     : https://prove2.me/theorems/4f8bd477-d861-4d98-a826-4b454b3485e6
-- title:
--   `BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero` (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (hherm : IsHermitianKernel a) (N : ℕ) : (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero` (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (hherm : IsHermitianKernel a) (N : ℕ) : (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * ∑ k ∈ range (N + 1), a n k * u k).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

theorem BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (hherm : IsHermitianKernel a)
    (N : ℕ) :
    (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) *
        ∑ k ∈ range (N + 1), a n k * u k).im = 0 := by sorry
