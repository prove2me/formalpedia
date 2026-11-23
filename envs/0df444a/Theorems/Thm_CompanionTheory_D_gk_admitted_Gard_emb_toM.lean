-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_emb_toM
-- name    : CompanionTheory.D.gk.admitted.Gard.emb_toM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:01.842179+00:00
-- url     : https://prove2.me/theorems/9ffa5fe2-f279-4a32-92de-416a82b96cbc
-- title:
--   Gard: emb to M
-- statement:
--   The Gard construction uses the emb to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Garding.lean#L37-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Garding.lean#L37-L37

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open CompanionTheory.D.gk.admitted.Gard
variable {n : ℕ} {ε : Fin n → Bool}

theorem CompanionTheory.D.gk.admitted.Gard.emb_toM : IsClosedEmbedding (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by sorry
