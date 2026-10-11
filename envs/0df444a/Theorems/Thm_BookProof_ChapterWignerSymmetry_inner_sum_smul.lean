-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_sum_smul
-- name    : BookProof.ChapterWignerSymmetry.inner_sum_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:18:26.999403+00:00
-- url     : https://prove2.me/theorems/291f617e-f729-41c8-b6f2-8dd6d1549872
-- title:
--   `BookProof.ChapterWignerSymmetry.inner_sum_smul` (b : OrthonormalBasis ι ℂ E) (v w : ι → ℂ) : ⟪∑ j, v j • b j, ∑ j, w j • b j⟫_ℂ = ∑ k, conj (v k) * w k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.inner_sum_smul` (b : OrthonormalBasis ι ℂ E) (v w : ι → ℂ) : ⟪∑ j, v j • b j, ∑ j, w j • b j⟫_ℂ = ∑ k, conj (v k) * w k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.inner_sum_smul`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.inner_sum_smul
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.inner_sum_smul (b : OrthonormalBasis ι ℂ E) (v w : ι → ℂ) :
    ⟪∑ j, v j • b j, ∑ j, w j • b j⟫_ℂ = ∑ k, conj (v k) * w k := by sorry
