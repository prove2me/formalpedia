-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_finite_rank_of_irreducible_unitary
-- name    : CompanionTheory.D.gk.admitted.finite_rank_of_irreducible_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:51:20.443915+00:00
-- url     : https://prove2.me/theorems/26e0f333-5ccf-4a2a-88c8-a857a3f198df
-- title:
--   admitted: finite rank of irreducible unitary
-- statement:
--   The admitted construction uses the finite rank of irreducible unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L309-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L309-L313

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted

theorem CompanionTheory.D.gk.admitted.finite_rank_of_irreducible_unitary : FinOfPI := by sorry
