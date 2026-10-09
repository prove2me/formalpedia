-- Prove2me | Theorems.Thm_BookProof_ChapterE3_euler_density_isIdempotent
-- name    : BookProof.ChapterE3.euler_density_isIdempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:13:14.563726+00:00
-- url     : https://prove2.me/theorems/7ee156a3-fae1-4e95-a664-5418297d2e45
-- title:
--   `BookProof.ChapterE3.euler_density_isIdempotent` (l w : Fin n → ℝ) (θ : ℝ) (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1) (hlw : ∑ i, l i * w i = 0) : (Matrix.vecMulVec (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE3`.
--
--   `BookProof.ChapterE3.euler_density_isIdempotent` (l w : Fin n → ℝ) (θ : ℝ) (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1) (hlw : ∑ i, l i * w i = 0) : (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i) (fun i => Real.cos θ * l i + Real.sin θ * w i)) * (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i) (fun i => Real.cos θ * l i + Real.sin θ * w i)) = Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i) (fun i => Real.cos θ * l i + Real.sin θ * w i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE3.euler_density_isIdempotent`.

-- Generated from ChapterE3.lean — theorem BookProof.ChapterE3.euler_density_isIdempotent
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3


open scoped Matrix BigOperators


variable {n : ℕ}

theorem BookProof.ChapterE3.euler_density_isIdempotent (l w : Fin n → ℝ) (θ : ℝ)
    (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1)
    (hlw : ∑ i, l i * w i = 0) :
    (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i))
      * (Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i))
      = Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i) := by sorry
