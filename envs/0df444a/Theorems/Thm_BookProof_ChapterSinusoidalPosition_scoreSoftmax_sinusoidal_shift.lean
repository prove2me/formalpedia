-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_scoreSoftmax_sinusoidal_shift
-- name    : BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:06:23.509975+00:00
-- url     : https://prove2.me/theorems/b2022911-d68b-44bb-8fe5-a6fa7b2993b6
-- title:
--   `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift` {m : ℕ} (beta : ℝ) (w : Fin n → ℝ) (p t : ℝ) (k : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => peInner w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift` {m : ℕ} (beta : ℝ) (w : Fin n → ℝ) (p t : ℝ) (k : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => peInner w (p + t) (k l + t)) j = scoreSoftmax beta (fun l => peInner w p (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

theorem BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift {m : ℕ} (beta : ℝ) (w : Fin n → ℝ) (p t : ℝ)
    (k : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => peInner w (p + t) (k l + t)) j
      = scoreSoftmax beta (fun l => peInner w p (k l)) j := by sorry
