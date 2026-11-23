-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_congr
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:45.066138+00:00
-- url     : https://prove2.me/theorems/0e80dd85-b685-4a3d-acea-1b7e1366a0f9
-- title:
--   Cholesky Decomposition: dp congr
-- statement:
--   The Cholesky Decomposition construction uses the dp congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L40-L50

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_congr {p : Fin n → Fin n} {α β α' β' : Fin n → ℂ}
    (h1 : ∀ i, p i = i → α i + β i = α' i + β' i) (h2 : ∀ i, p i ≠ i → α i = α' i ∧ β i = β' i) :
    dp p α β = dp p α' β' := by sorry
