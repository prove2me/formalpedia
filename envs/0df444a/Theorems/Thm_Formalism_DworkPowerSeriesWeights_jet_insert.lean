-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_insert
-- name    : Formalism.DworkPowerSeriesWeights.jet_insert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:05.752363+00:00
-- url     : https://prove2.me/theorems/c41c83ab-3b90-47b3-91ce-507500711b3a
-- title:
--   Dwork Power Series Weights: jet insert
-- statement:
--   The Dwork Power Series Weights construction uses the jet insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L134-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L134-L151

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

theorem Formalism.DworkPowerSeriesWeights.jet_insert {α : Type} [DecidableEq α] (c : ι → ι → K) (S : K) (L : α → ι → K) (a : α)
    (s : Finset α) (ha : a ∉ s) (h : MvPowerSeries ι K) :
    jetPair (∏ i ∈ insert a s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * dirD (L a) h) +
        ∑ b ∈ s, (-S * polar c (L a) (L b)) *
          jetPair (∏ i ∈ s.erase b, linForm (L i)) (mvExp ((-S) • quadSer c) * h) := by sorry
