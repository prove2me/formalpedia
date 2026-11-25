-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_TwInt_bdd_dsW
-- name    : CompanionTheory.D.gk.FinalFormK.TwInt.bdd_dsW
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:04.4389+00:00
-- url     : https://prove2.me/theorems/d9fc95b2-4881-4c42-aeb9-56cbeaa1d7e6
-- title:
--   Tw Int: bdd ds W
-- statement:
--   The Tw Int construction uses the bdd ds W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L256-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L256-L287

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → ι → ι → ℂ} {T : ι → H → H'}

theorem CompanionTheory.D.gk.FinalFormK.TwInt.bdd_dsW (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hτ : RepOn G τ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {W : List (Mat n)} (hW : ∀ X ∈ W, L X) (c : ι) : Bdd G L σ fun v => dsW τ W (T c v) := by sorry
