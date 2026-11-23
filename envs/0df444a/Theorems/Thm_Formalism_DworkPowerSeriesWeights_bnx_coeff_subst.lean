-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_coeff_subst
-- name    : Formalism.DworkPowerSeriesWeights.bnx_coeff_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:23.696062+00:00
-- url     : https://prove2.me/theorems/2f2a4586-acef-4411-b5dd-ae029cdfd57d
-- title:
--   Dwork Power Series Weights: bnx coeff subst
-- statement:
--   The Dwork Power Series Weights construction uses the bnx coeff subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L209-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L209-L240

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
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.bnx_coeff_subst (a b : ZMod d → K) (f : MvPowerSeries (ZMod d) K) (m : V2 d →₀ ℕ) :
    coeff m (subst (bnxA a b) f) = coeff (bnxN m) f *
      ∏ s, (a s ^ m (false, s) * b s ^ m (true, s) *
        ((m (false, s) + m (true, s)).choose (m (false, s)) : K)) := by sorry
