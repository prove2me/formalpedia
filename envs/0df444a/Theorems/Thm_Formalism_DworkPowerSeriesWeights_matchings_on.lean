-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_matchings_on
-- name    : Formalism.DworkPowerSeriesWeights.matchings_on
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:39.732004+00:00
-- url     : https://prove2.me/theorems/6aeb0b90-addd-4a20-98c3-200bdb9f4e31
-- title:
--   Dwork Power Series Weights: matchings on
-- statement:
--   The Dwork Power Series Weights construction uses the matchings on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L326-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L326-L350

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
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.matchings_on (c : ι → ι → K) (S : K) {n : ℕ} (L : Fin n → ι → K) (s : Finset (Fin n)) :
    ∀ h : MvPowerSeries ι K,
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
        ∑ σ ∈ invOn s, edgeW (fun i j => -S * polar c (L i) (L j)) σ *
          jetPair (∏ i ∈ s.filter (fun i => σ i = i), linForm (L i)) h := by sorry
