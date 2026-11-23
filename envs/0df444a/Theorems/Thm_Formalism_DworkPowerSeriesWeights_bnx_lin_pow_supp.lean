-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow_supp
-- name    : Formalism.DworkPowerSeriesWeights.bnx_lin_pow_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:38.534948+00:00
-- url     : https://prove2.me/theorems/41050d7c-8b93-4373-8016-9ee646f873ad
-- title:
--   Dwork Power Series Weights: bnx lin pow supp
-- statement:
--   The Dwork Power Series Weights construction uses the bnx lin pow supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L67-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L67-L79

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

theorem Formalism.DworkPowerSeriesWeights.bnx_lin_pow_supp {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ)
    (a b : K) (k : ℕ) (μ : σ →₀ ℕ)
    (h : coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) ≠ 0) (z : σ) (hz : μ z ≠ 0) :
    z = x ∨ z = y := by sorry
