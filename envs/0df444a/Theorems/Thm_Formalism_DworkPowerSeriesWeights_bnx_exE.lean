-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_exE
-- name    : Formalism.DworkPowerSeriesWeights.bnx_exE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:36.553799+00:00
-- url     : https://prove2.me/theorems/fde8b563-4835-4603-ab3c-7e732207e5f9
-- title:
--   Dwork Power Series Weights: bnx ex E
-- statement:
--   The Dwork Power Series Weights construction uses the bnx ex E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L737-L747
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L737-L747

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

theorem Formalism.DworkPowerSeriesWeights.bnx_exE {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degE n) :
    ∃ s : ZMod d, s.val % 2 = 0 ∧ n s ≠ 0 := by sorry
