-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow
-- name    : Formalism.DworkPowerSeriesWeights.bnx_lin_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:44.231909+00:00
-- url     : https://prove2.me/theorems/f73fbb73-4f5a-4ea4-bd52-99c5743eecf2
-- title:
--   Dwork Power Series Weights: bnx lin pow
-- statement:
--   The Dwork Power Series Weights construction uses the bnx lin pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L13-L30

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
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
open MvPowerSeries Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.bnx_lin_pow {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ)
    (μ : σ →₀ ℕ) :
    coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      ∑ r ∈ Finset.range (k + 1),
        if Finsupp.single x r + Finsupp.single y (k - r) = μ then
          a ^ r * b ^ (k - r) * (k.choose r : K) else 0 := by sorry
