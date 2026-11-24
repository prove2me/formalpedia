-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_quad_pow
-- name    : Formalism.DworkPowerSeriesWeights.quad_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:44:26.022078+00:00
-- url     : https://prove2.me/theorems/30e93377-9f4b-4419-81ec-d3f5e9c441c8
-- title:
--   Dwork Power Series Weights: quad pow
-- statement:
--   The Dwork Power Series Weights construction uses the quad pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L46-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean#L46-L62

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.DworkPowerSeriesWeights.quad_pow {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → K) (k : ℕ) :
    (∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) :
      MvPowerSeries (Bool × ι) K) ^ k =
    ∑ n ∈ Finset.piAntidiag Finset.univ k, (Nat.multinomial Finset.univ n : MvPowerSeries (Bool × ι) K) *
      MvPowerSeries.monomial (pairExp n) (∏ i, u i ^ n i) := by sorry
