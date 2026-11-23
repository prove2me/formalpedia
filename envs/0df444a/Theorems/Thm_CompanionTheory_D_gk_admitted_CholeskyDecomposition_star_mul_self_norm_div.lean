-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_star_mul_self_norm_div
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.star_mul_self_norm_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:34.163137+00:00
-- url     : https://prove2.me/theorems/e471c045-56df-40fd-a751-c6b09fbc256a
-- title:
--   Cholesky Decomposition: star mul self norm div
-- statement:
--   The Cholesky Decomposition construction uses the star mul self norm div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaChol.lean#L64-L67

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.star_mul_self_norm_div {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by sorry
