-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
-- name    : CompanionTheory.D.Upq.Sm.dsW_cons
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:43.79245+00:00
-- url     : https://prove2.me/theorems/1b604435-4343-4beb-ae49-8a372ca09181
-- title:
--   Sm: ds W cons
-- statement:
--   The Sm construction uses the ds W cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L114-L115

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem CompanionTheory.D.Upq.Sm.dsW_cons (σ : Mat n → (H →L[ℂ] H)) (X : Mat n) (W : List (Mat n)) (v : H) :
    dsW σ (X :: W) v = ds σ X (dsW σ W v) := by sorry
