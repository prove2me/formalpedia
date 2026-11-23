-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_apply
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:37.101014+00:00
-- url     : https://prove2.me/theorems/165a05d0-bdc7-4260-a934-20cabf5805fa
-- title:
--   Cholesky Decomposition: dp mul apply
-- statement:
--   The Cholesky Decomposition construction uses the dp mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L15-L17

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_apply (p : Fin n → Fin n) (α β : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p α β * X) i j = α i * X i j + β i * X (p i) j := by sorry
