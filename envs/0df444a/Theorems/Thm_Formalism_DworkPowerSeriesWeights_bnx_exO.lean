-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_exO
-- name    : Formalism.DworkPowerSeriesWeights.bnx_exO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:54.405139+00:00
-- url     : https://prove2.me/theorems/9248bb5c-057a-4853-aeed-116714bf33a9
-- title:
--   Dwork Power Series Weights: bnx ex O
-- statement:
--   The Dwork Power Series Weights construction uses the bnx ex O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L749-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L749-L759

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

theorem Formalism.DworkPowerSeriesWeights.bnx_exO {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degO n) :
    ∃ s : ZMod d, s.val % 2 ≠ 0 ∧ n s ≠ 0 := by sorry
