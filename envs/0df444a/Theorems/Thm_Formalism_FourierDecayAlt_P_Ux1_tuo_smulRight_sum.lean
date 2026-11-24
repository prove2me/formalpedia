-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tuo_smulRight_sum
-- name    : Formalism.FourierDecayAlt.P.Ux1.tuo_smulRight_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:10:27.572176+00:00
-- url     : https://prove2.me/theorems/bac3da9a-8393-482d-b6f7-2fac16cc025e
-- title:
--   Ux1: tuo smul Right sum
-- statement:
--   The Ux1 construction uses the tuo smul Right sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L23-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L23-L55

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

theorem Formalism.FourierDecayAlt.P.Ux1.tuo_smulRight_sum {Ω : Set 𝔤} (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ)) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B)
    (Ψ : ι → ℕ → 𝔤 → E) (L : ι → 𝔤 → E) (h : ∀ i, TendstoUniformlyOn (Ψ i) (L i) atTop Ω) :
    TendstoUniformlyOn (fun n Y => ∑ i, (a i Y).smulRight (Ψ i n Y))
      (fun Y => ∑ i, (a i Y).smulRight (L i Y)) atTop Ω := by sorry
