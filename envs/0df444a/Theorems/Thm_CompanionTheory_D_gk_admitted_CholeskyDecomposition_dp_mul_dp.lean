-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_dp
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_dp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:42.314874+00:00
-- url     : https://prove2.me/theorems/937c5c1b-c52e-4b59-b28b-70eb6d32c295
-- title:
--   Cholesky Decomposition: dp mul dp
-- statement:
--   The Cholesky Decomposition construction uses the dp mul dp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L19-L25

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_dp {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β α' β' : Fin n → ℂ) :
    dp p α β * dp p α' β' =
      dp p (fun i => α i * α' i + β i * β' (p i)) (fun i => α i * β' i + β i * α' (p i)) := by sorry
