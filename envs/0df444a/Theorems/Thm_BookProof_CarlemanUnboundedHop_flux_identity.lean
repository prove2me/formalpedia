-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_flux_identity
-- name    : BookProof.CarlemanUnboundedHop.flux_identity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:32:29.802275+00:00
-- url     : https://prove2.me/theorems/319e91f6-0395-4c36-88a2-4ef934691b93
-- title:
--   `BookProof.CarlemanUnboundedHop.flux_identity` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z) (N : ℕ) : z.im * ∑ n ∈ range...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.flux_identity` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z) (N : ℕ) : z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 = (flux a u N).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.flux_identity`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.flux_identity
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

theorem BookProof.CarlemanUnboundedHop.flux_identity {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hherm : IsHermitianKernel a)
    (hrec : LadderRecInf a u z) (N : ℕ) :
    z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 = (flux a u N).im := by sorry
