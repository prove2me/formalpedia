-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_TwInt_isSm
-- name    : CompanionTheory.D.gk.FinalFormK.TwInt.isSm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:00.029191+00:00
-- url     : https://prove2.me/theorems/49046184-819d-4dfc-92a7-75b9f00ce1f2
-- title:
--   Tw Int: is Sm
-- statement:
--   The Tw Int construction uses the is Sm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L237-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L237-L240

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
omit [DecidableEq ι]

theorem CompanionTheory.D.gk.FinalFormK.TwInt.isSm (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (c : ι) {v : H} (hv : IsSm G σ v) : IsSm G τ (T c v) := by sorry
