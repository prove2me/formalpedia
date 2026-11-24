-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_AL
-- name    : Formalism.FourierDecayAlt.P.Ux1.AL
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:00.123797+00:00
-- url     : https://prove2.me/theorems/881968b8-8b2b-4fbb-bb60-d943d890ca98
-- title:
--   Ux1: AL
-- statement:
--   The Ux1 construction uses the AL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L57-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L57-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem Formalism.FourierDecayAlt.P.Ux1.AL {Ω : Set 𝔤} (hΩ : IsOpen Ω) (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ))
    (ha : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a i) Ω) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B) :
    ∀ (m : ℕ) (Ψ : List ι → ℕ → 𝔤 → E) (L : List ι → 𝔤 → E),
      (∀ w : List ι, w.length ≤ m → ∀ n, ContinuousOn (Ψ w n) Ω) →
      (∀ w : List ι, w.length < m → ∀ n, ∀ Y ∈ Ω,
        HasFDerivAt (Ψ w n) (∑ i, (a i Y).smulRight (Ψ (i :: w) n Y)) Y) →
      (∀ w : List ι, w.length ≤ m → TendstoUniformlyOn (Ψ w) (L w) atTop Ω) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (L []) Ω := by sorry
