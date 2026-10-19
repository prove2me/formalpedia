-- Prove2me | Theorems.Thm_BookProof_ChapterSinusoidalPosition_scoreSoftmax_sinusoidal_ge
-- name    : BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:08:57.468686+00:00
-- url     : https://prove2.me/theorems/b97833d3-48d7-427b-8a57-6014a012cbdf
-- title:
--   `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge` {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (w : Fin n → ℝ) (p : ℝ) (k : Fin m → ℝ) (j : Fin m) : Real.exp (-(beta * (2 * n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSinusoidalPosition`.
--
--   `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge` {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (w : Fin n → ℝ) (p : ℝ) (k : Fin m → ℝ) (j : Fin m) : Real.exp (-(beta * (2 * n))) / (m : ℝ) ≤ scoreSoftmax beta (fun l => peInner w p (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge`.

-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge
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

theorem BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (w : Fin n → ℝ)
    (p : ℝ) (k : Fin m → ℝ) (j : Fin m) :
    Real.exp (-(beta * (2 * n))) / (m : ℝ)
      ≤ scoreSoftmax beta (fun l => peInner w p (k l)) j := by sorry
