-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_wigner_symmetry
-- name    : BookProof.ChapterWignerSymmetry.wigner_symmetry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:06.478989+00:00
-- url     : https://prove2.me/theorems/90901c27-bc3d-467c-8eb7-8fd125c7176b
-- title:
--   `BookProof.ChapterWignerSymmetry.wigner_symmetry` (b : OrthonormalBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T) : (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x =...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.wigner_symmetry` (b : OrthonormalBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T) : (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨ (∃ U : E → E, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.wigner_symmetry`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.wigner_symmetry
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

theorem BookProof.ChapterWignerSymmetry.wigner_symmetry (b : OrthonormalBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : E → E, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by sorry
