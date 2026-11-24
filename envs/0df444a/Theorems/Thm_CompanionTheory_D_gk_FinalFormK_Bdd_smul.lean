-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
-- name    : CompanionTheory.D.gk.FinalFormK.Bdd.smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:00.907548+00:00
-- url     : https://prove2.me/theorems/f7aee8a6-4630-40ac-aeb4-693f0a3cac34
-- title:
--   Bdd: smul
-- statement:
--   The Bdd construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L59-L64

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}

theorem CompanionTheory.D.gk.FinalFormK.Bdd.smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : H → E} (h : Bdd G L σ T) (a : ℂ) :
    Bdd G L σ fun v => a • T v := by sorry
