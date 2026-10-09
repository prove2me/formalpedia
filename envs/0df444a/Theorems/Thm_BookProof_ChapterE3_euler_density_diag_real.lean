-- Prove2me | Theorems.Thm_BookProof_ChapterE3_euler_density_diag_real
-- name    : BookProof.ChapterE3.euler_density_diag_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:56.979289+00:00
-- url     : https://prove2.me/theorems/8be49162-bb9a-4108-9397-8176b191cc10
-- title:
--   `BookProof.ChapterE3.euler_density_diag_real` (l w : Fin n → ℝ) (θ : ℝ) (i : Fin n) (hli : l i = 1) (hwi : w i = 0) : Matrix.vecMulVec (fun j => Real.cos θ * l j + Real.sin θ * w j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE3`.
--
--   `BookProof.ChapterE3.euler_density_diag_real` (l w : Fin n → ℝ) (θ : ℝ) (i : Fin n) (hli : l i = 1) (hwi : w i = 0) : Matrix.vecMulVec (fun j => Real.cos θ * l j + Real.sin θ * w j) (fun j => Real.cos θ * l j + Real.sin θ * w j) i i = Real.cos θ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE3.euler_density_diag_real`.

-- Generated from ChapterE3.lean — theorem BookProof.ChapterE3.euler_density_diag_real
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3


open scoped Matrix BigOperators


variable {n : ℕ}

theorem BookProof.ChapterE3.euler_density_diag_real (l w : Fin n → ℝ) (θ : ℝ) (i : Fin n)
    (hli : l i = 1) (hwi : w i = 0) :
    Matrix.vecMulVec (fun j => Real.cos θ * l j + Real.sin θ * w j)
        (fun j => Real.cos θ * l j + Real.sin θ * w j) i i
      = Real.cos θ ^ 2 := by sorry
