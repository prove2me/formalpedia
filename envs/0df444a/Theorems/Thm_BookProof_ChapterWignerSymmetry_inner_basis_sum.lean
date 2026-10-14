-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_basis_sum
-- name    : BookProof.ChapterWignerSymmetry.inner_basis_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:18:09.539185+00:00
-- url     : https://prove2.me/theorems/f63562be-ff9b-4797-a0a7-b2e1d46c4970
-- title:
--   `BookProof.ChapterWignerSymmetry.inner_basis_sum` (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (k : ι) : ⟪b k, ∑ j, v j • b j⟫_ℂ = v k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.inner_basis_sum` (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (k : ι) : ⟪b k, ∑ j, v j • b j⟫_ℂ = v k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.inner_basis_sum`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.inner_basis_sum
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.inner_basis_sum (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (k : ι) :
    ⟪b k, ∑ j, v j • b j⟫_ℂ = v k := by sorry
