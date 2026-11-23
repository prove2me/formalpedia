-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_evenDerivative_binomial_coeff
-- name    : Formalism.DworkPowerSeriesWeights.evenDerivative_binomial_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:35.568497+00:00
-- url     : https://prove2.me/theorems/347d917b-7643-4cac-bc94-747e37a59fb0
-- title:
--   Dwork Power Series Weights: even Derivative binomial coeff
-- statement:
--   The Dwork Power Series Weights construction uses the even Derivative binomial coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L327-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L327-L354

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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

theorem Formalism.DworkPowerSeriesWeights.evenDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de1 be) = coeff n be * ((n s).choose j : K) := by sorry
