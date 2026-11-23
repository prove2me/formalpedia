-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_conjTranspose
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:52.561707+00:00
-- url     : https://prove2.me/theorems/a992e4f9-0748-4d1f-ae42-0bd7e52f1393
-- title:
--   Cholesky Decomposition: dp conj Transpose
-- statement:
--   The Cholesky Decomposition construction uses the dp conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L27-L38

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_conjTranspose {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β : Fin n → ℂ) :
    (dp p α β)ᴴ = dp p (fun i => star (α i)) (fun i => star (β (p i))) := by sorry
