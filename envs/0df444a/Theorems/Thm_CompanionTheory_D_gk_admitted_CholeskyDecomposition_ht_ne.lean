-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_ht_ne
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.ht_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:33.32355+00:00
-- url     : https://prove2.me/theorems/080cfe60-4a5e-4528-b10d-91ae07677f78
-- title:
--   Cholesky Decomposition: ht ne
-- statement:
--   The Cholesky Decomposition construction uses the ht ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaAll.lean#L34-L41

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.ht_ne {ε : Fin n → Bool} {i : Fin n} (h : ε i.rev ≠ ε i) : 2 * (i : ℤ) + 1 - n ≠ 0 := by sorry
