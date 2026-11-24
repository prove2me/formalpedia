-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_FinalFormK_exists_factor
-- name    : CompanionTheory.D.gk.FinalFormK.exists_factor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:00.852805+00:00
-- url     : https://prove2.me/theorems/cad7972e-8cf5-4978-b272-f3195f03735a
-- title:
--   Final Form K: exists factor
-- statement:
--   The Final Form K construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L87-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean#L87-L133

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

theorem CompanionTheory.D.gk.FinalFormK.exists_factor [CompleteSpace H] [CompleteSpace H'] {T : H → H'} (hl : Lin G σ T) (hσ : RepOn G σ) {C : ℝ}
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i))
    (hb : ∀ v, IsSm G σ v → ‖T v‖ ≤ C * ∑ i, ‖dsW σ (W i) v‖) :
    ∃ Λ : ι → (H →L[ℂ] H'), ∀ v, IsSm G σ v → T v = ∑ i, Λ i (dsW σ (W i) v) := by sorry
