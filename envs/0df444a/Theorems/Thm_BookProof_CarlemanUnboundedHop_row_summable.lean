-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_row_summable
-- name    : BookProof.CarlemanUnboundedHop.row_summable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:34.339091+00:00
-- url     : https://prove2.me/theorems/2b55584b-31c3-4641-aa4d-89635b410b36
-- title:
--   `BookProof.CarlemanUnboundedHop.row_summable` {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (k : ℕ) : Summable fun n : ℕ => ‖a k n‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.row_summable` {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (k : ℕ) : Summable fun n : ℕ => ‖a k n‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.row_summable`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.row_summable
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.row_summable {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (k : ℕ) :
    Summable fun n : ℕ => ‖a k n‖ ^ 2 := by sorry
