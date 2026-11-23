-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_prod_choose
-- name    : Formalism.DworkPowerSeriesWeights.bnx_prod_choose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:40.485491+00:00
-- url     : https://prove2.me/theorems/06d5ab0f-c0e7-4b3e-be25-5a84a809e738
-- title:
--   Dwork Power Series Weights: bnx prod choose
-- statement:
--   The Dwork Power Series Weights construction uses the bnx prod choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L312-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L312-L325

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

theorem Formalism.DworkPowerSeriesWeights.bnx_prod_choose (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) (e : ZMod d → K)
    (he : e s = 1) :
    ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * e t ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = ((n s).choose j : K) := by sorry
