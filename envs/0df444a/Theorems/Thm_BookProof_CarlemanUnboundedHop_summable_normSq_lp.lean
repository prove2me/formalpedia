-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_summable_normSq_lp
-- name    : BookProof.CarlemanUnboundedHop.summable_normSq_lp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:52.531407+00:00
-- url     : https://prove2.me/theorems/a3cc97c9-28e8-49fc-820d-f1c4a20cd390
-- title:
--   `BookProof.CarlemanUnboundedHop.summable_normSq_lp` (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.summable_normSq_lp` (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.summable_normSq_lp`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.summable_normSq_lp
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.summable_normSq_lp (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2 := by sorry
