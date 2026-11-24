-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_hasDerivAt
-- name    : CompanionTheory.D.gk.FinalFormK.Bdd.hasDerivAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:29.402796+00:00
-- url     : https://prove2.me/theorems/3f0dd51a-f966-4b2b-b106-06fd0698048b
-- title:
--   Bdd: has Deriv At
-- statement:
--   The Bdd construction uses the has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L214-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L214-L226

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt

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

theorem CompanionTheory.D.gk.FinalFormK.Bdd.hasDerivAt {T : H → H'} (hb : Bdd G L σ T) (hl : Lin G σ T) (hσ : RepOn G σ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v})
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => T (σ (ex X t) v)) (T (ds σ X v)) 0 := by sorry
