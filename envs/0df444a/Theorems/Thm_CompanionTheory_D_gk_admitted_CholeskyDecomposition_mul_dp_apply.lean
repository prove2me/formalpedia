-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_mul_dp_apply
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.mul_dp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:45.725318+00:00
-- url     : https://prove2.me/theorems/d6978b5b-c84f-48a7-af9a-0f951de4dbf7
-- title:
--   Cholesky Decomposition: mul dp apply
-- statement:
--   The Cholesky Decomposition construction uses the mul dp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L58-L65

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.mul_dp_apply {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (β : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : (X * dp p 0 β) i j = X i (p j) * β (p j) := by sorry
