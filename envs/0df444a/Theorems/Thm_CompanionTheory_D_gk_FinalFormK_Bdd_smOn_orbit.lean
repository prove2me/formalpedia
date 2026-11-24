-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smOn_orbit
-- name    : CompanionTheory.D.gk.FinalFormK.Bdd.smOn_orbit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:12.240244+00:00
-- url     : https://prove2.me/theorems/5862686f-5b0a-4b19-a1bc-c7c1e60b2de8
-- title:
--   Bdd: sm On orbit
-- statement:
--   The Bdd construction uses the sm On orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L206-L212

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
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
variable [CompleteSpace H] [CompleteSpace H']

theorem CompanionTheory.D.gk.FinalFormK.Bdd.smOn_orbit {T : H → H'} (hb : Bdd G L σ T) (hl : Lin G σ T) (hσ : RepOn G σ)
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : SmOn G fun g => T (σ g v) := by sorry
