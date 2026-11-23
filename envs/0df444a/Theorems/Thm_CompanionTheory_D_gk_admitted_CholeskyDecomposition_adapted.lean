-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_adapted
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.adapted
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:22.570481+00:00
-- url     : https://prove2.me/theorems/9e4540a0-e18d-4c6d-9aad-4c58da0cbaa1
-- title:
--   Cholesky Decomposition: adapted
-- statement:
--   The Cholesky Decomposition construction uses the adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L60-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L60-L137

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
open CompanionTheory.D.gk.admitted.CholeskyDecomposition
variable {n : ℕ}

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.adapted {ε : Fin n → Bool} (hε : Monotone ε) : Adapted (pr ε) (ht ε) (wt ε) := by sorry
