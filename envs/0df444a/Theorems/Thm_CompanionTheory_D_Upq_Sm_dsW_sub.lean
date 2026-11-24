-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_sub
-- name    : CompanionTheory.D.Upq.Sm.dsW_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:42.415264+00:00
-- url     : https://prove2.me/theorems/87dfbe3d-37d2-402b-b978-d02149a9c118
-- title:
--   Sm: ds W sub
-- statement:
--   The Sm construction uses the ds W sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L226-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L226-L229

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

theorem CompanionTheory.D.Upq.Sm.dsW_sub (h : RepOn G σ) {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v')
    {W : List (Mat n)} (hW : LieW G W) : dsW σ W (v - v') = dsW σ W v - dsW σ W v' := by sorry
