-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_summable_cutMass
-- name    : BookProof.CarlemanUnboundedHop.summable_cutMass
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:22.066064+00:00
-- url     : https://prove2.me/theorems/226c6bda-4c72-4903-a73b-4b83515e10fe
-- title:
--   `BookProof.CarlemanUnboundedHop.summable_cutMass` (hu : Summable fun n => ‖u n‖ ^ 2) (hΘ0 : ∀ j, 0 ≤ Θ j) (hΘsum : Summable Θ) : Summable (fun N => cutMass u Θ N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.summable_cutMass` (hu : Summable fun n => ‖u n‖ ^ 2) (hΘ0 : ∀ j, 0 ≤ Θ j) (hΘsum : Summable Θ) : Summable (fun N => cutMass u Θ N)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.summable_cutMass`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.summable_cutMass
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.summable_cutMass (hu : Summable fun n => ‖u n‖ ^ 2) (hΘ0 : ∀ j, 0 ≤ Θ j)
    (hΘsum : Summable Θ) : Summable (fun N => cutMass u Θ N) := by sorry
