-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_eq_one_of_posSemidef
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_one_of_posSemidef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:51.789395+00:00
-- url     : https://prove2.me/theorems/c281495a-8603-41ef-8c1f-8f2ddc90c8d8
-- title:
--   Cholesky Decomposition: eq one of pos Semidef
-- statement:
--   The Cholesky Decomposition construction uses the eq one of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L78-L83

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_one_of_posSemidef {w : Matrix (Fin n) (Fin n) ℂ} (h1 : wᴴ * w = 1) (hw : w.PosSemidef) : w = 1 := by sorry
