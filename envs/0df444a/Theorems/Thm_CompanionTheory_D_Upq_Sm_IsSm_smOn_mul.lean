-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smOn_mul
-- name    : CompanionTheory.D.Upq.Sm.IsSm.smOn_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:50.716272+00:00
-- url     : https://prove2.me/theorems/966fae4c-d685-4515-93a8-50f1f440e06b
-- title:
--   Is Sm: sm On mul
-- statement:
--   The Is Sm construction uses the sm On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L188-L191

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
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem CompanionTheory.D.Upq.Sm.IsSm.smOn_mul (h : RepOn G σ) {w : H} (hw : IsSm G σ w) :
    SmOn (G ×ˢ G) (fun q : Mat n × Mat n => σ q.1 (σ q.2 w)) := by sorry
