-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_true
-- name    : Formalism.DworkPowerSeriesWeights.bnxM_true
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:39.183195+00:00
-- url     : https://prove2.me/theorems/36c7ca07-cc87-44f6-8531-aff3f5b7c277
-- title:
--   Dwork Power Series Weights: bnx M true
-- statement:
--   The Dwork Power Series Weights construction uses the bnx M true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L278-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L278-L282

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

theorem Formalism.DworkPowerSeriesWeights.bnxM_true (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) :
    bnxM n k (true, s) = n s - k s := by sorry
