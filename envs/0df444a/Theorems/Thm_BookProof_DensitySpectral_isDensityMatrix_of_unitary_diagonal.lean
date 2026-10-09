-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_isDensityMatrix_of_unitary_diagonal
-- name    : BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:57:01.849925+00:00
-- url     : https://prove2.me/theorems/fd0eb837-fb19-439a-a221-bd210b049f57
-- title:
--   `BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal` (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i = 1) : IsDensityMatrix ((U : Matrix n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensitySpectral`.
--
--   `BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal` (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i = 1) : IsDensityMatrix ((U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) * (U : Matrix n n ℂ)ᴴ)
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal`.

-- Generated from ChapterDensitySpectral.lean — theorem BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal
import Mathlib
import Definitions.Def_ChapterDensitySpectral
import Definitions.Def_ChapterB4
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.ChapterB4
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.isDensityMatrix_of_unitary_diagonal
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i = 1) :
    IsDensityMatrix ((U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d)
      * (U : Matrix n n ℂ)ᴴ) := by sorry
