-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_prod_lin_mul
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_prod_lin_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:11.235806+00:00
-- url     : https://prove2.me/theorems/6e56b6ef-6193-4fb9-bc31-6308da76ddf9
-- title:
--   Dwork Power Series Weights: jet Pair prod lin mul
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair prod lin mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L91-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L91-L109

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.jetPair_prod_lin_mul {α : Type} [DecidableEq α] (L : α → ι → K) (ℓ : MvPowerSeries ι K)
    (cst : α → K) (h0 : MvPowerSeries.constantCoeff ℓ = 0)
    (hd : ∀ a, dirD (L a) ℓ = MvPowerSeries.C (cst a)) (s : Finset α) :
    ∀ G : MvPowerSeries ι K, jetPair (∏ i ∈ s, linForm (L i)) (ℓ * G) =
      ∑ b ∈ s, cst b * jetPair (∏ i ∈ s.erase b, linForm (L i)) G := by sorry
