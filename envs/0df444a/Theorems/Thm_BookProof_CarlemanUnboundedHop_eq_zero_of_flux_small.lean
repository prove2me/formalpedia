-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_eq_zero_of_flux_small
-- name    : BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:38.480986+00:00
-- url     : https://prove2.me/theorems/00f3dea7-79cc-489b-af78-732279f0cc0b
-- title:
--   `BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z) (hsmall...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z) (hsmall : ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ‖flux a u N‖ < ε) : ∀ n, u n = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

theorem BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hsmall : ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ‖flux a u N‖ < ε) :
    ∀ n, u n = 0 := by sorry
