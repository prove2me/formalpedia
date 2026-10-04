-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_symmetricOn_of_diagonal
-- name    : BookProof.HyperbolicQuadratic.symmetricOn_of_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:40:40.187433+00:00
-- url     : https://prove2.me/theorems/a6571793-f85e-4b37-b6da-3255930335fd
-- title:
--   The Lean 4 theorem `symmetricOn_of_diagonal` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `symmetricOn_of_diagonal` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.symmetricOn_of_diagonal
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HyperbolicQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

theorem BookProof.HyperbolicQuadratic.symmetricOn_of_diagonal (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hD : Submodule.span ℂ (Set.range v) = D)
    (T : D →ₗ[ℂ] E)
    (hT : ∀ (i : ι) (h : v i ∈ D), T ⟨v i, h⟩ = ((lam i : ℝ) : ℂ) • v i) :
    SymmetricOn D T := by sorry
