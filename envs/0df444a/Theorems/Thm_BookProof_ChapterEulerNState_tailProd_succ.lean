-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_tailProd_succ
-- name    : BookProof.ChapterEulerNState.tailProd_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:31:59.469209+00:00
-- url     : https://prove2.me/theorems/ae643dfc-218c-4dce-9121-fffedf462ca2
-- title:
--   `BookProof.ChapterEulerNState.tailProd_succ` (θ : ℕ → ℝ) (m : ℕ) : tailProd θ (m + 1) = tailProd θ m * Real.sin (θ m) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.tailProd_succ` (θ : ℕ → ℝ) (m : ℕ) : tailProd θ (m + 1) = tailProd θ m * Real.sin (θ m) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.tailProd_succ`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.tailProd_succ
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.tailProd_succ (θ : ℕ → ℝ) (m : ℕ) :
    tailProd θ (m + 1) = tailProd θ m * Real.sin (θ m) ^ 2 := by sorry
