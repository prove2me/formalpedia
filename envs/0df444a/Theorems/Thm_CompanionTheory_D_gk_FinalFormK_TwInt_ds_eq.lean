-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_TwInt_ds_eq
-- name    : CompanionTheory.D.gk.FinalFormK.TwInt.ds_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:53.809976+00:00
-- url     : https://prove2.me/theorems/47bf30d3-bda8-47bd-9ff0-d884c8980801
-- title:
--   Tw Int: ds eq
-- statement:
--   The Tw Int construction uses the ds eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L242-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L242-L254

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

theorem CompanionTheory.D.gk.FinalFormK.TwInt.ds_eq (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {X : Mat n} (hX : ∀ t, ex X t ∈ G) {M' : ι → ι → ℂ}
    (hM' : ∀ c d, HasDerivAt (fun t => M (ex X t) c d) (M' c d) 0) (c : ι) {v : H} (hv : IsSm G σ v) :
    ds τ X (T c v) = T c (ds σ X v) + ∑ d, M' c d • T d v := by sorry
