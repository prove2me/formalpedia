-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_isUpperTriangular_conjTranspose_iff
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.isUpperTriangular_conjTranspose_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:30.286106+00:00
-- url     : https://prove2.me/theorems/a83fc50c-3760-46b7-8c52-bab40409ea88
-- title:
--   Cholesky Decomposition: is Upper Triangular conj Transpose iff
-- statement:
--   The Cholesky Decomposition construction uses the is Upper Triangular conj Transpose iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L12-L20

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.isUpperTriangular_conjTranspose_iff {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by sorry
