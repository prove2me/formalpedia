-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_lt_of_sign
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.lt_of_sign
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:29.666562+00:00
-- url     : https://prove2.me/theorems/a7e6f28d-2b7a-47cc-abc0-61dc2cc97a2c
-- title:
--   Cholesky Decomposition: lt of sign
-- statement:
--   The Cholesky Decomposition construction uses the lt of sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L50-L58

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.lt_of_sign {ε : Fin n → Bool} (hε : Monotone ε) {i j : Fin n} (hi : ε i = false) (hj : ε j = true) :
    (i : ℤ) < j := by sorry
