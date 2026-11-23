-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_hs_eq_trace
-- name    : CompanionTheory.D.gk.admitted.Gard.hs_eq_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:58.674521+00:00
-- url     : https://prove2.me/theorems/609d517e-ab01-443d-b14b-2bec782145a8
-- title:
--   Gard: hs eq trace
-- statement:
--   The Gard construction uses the hs eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L29-L35

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem CompanionTheory.D.gk.admitted.Gard.hs_eq_trace (y : Matrix (Fin n) (Fin n) ℂ) : (hs y : ℂ) = (y * yᴴ).trace := by sorry
