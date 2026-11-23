-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_exists_cholesky
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:00.265299+00:00
-- url     : https://prove2.me/theorems/d4fd5510-3a02-4637-ae17-ef0f4d6bc68c
-- title:
--   Cholesky Decomposition: exists cholesky
-- statement:
--   The Cholesky Decomposition construction uses the exists cholesky property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L69-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L69-L86

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
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by sorry
