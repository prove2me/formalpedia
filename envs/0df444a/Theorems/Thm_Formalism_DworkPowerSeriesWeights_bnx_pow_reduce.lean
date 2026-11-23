-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_pow_reduce
-- name    : Formalism.DworkPowerSeriesWeights.bnx_pow_reduce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:45.057894+00:00
-- url     : https://prove2.me/theorems/df8da664-bf8a-45d4-a5d5-51627ad8ae35
-- title:
--   Dwork Power Series Weights: bnx pow reduce
-- statement:
--   The Dwork Power Series Weights construction uses the bnx pow reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L545-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L545-L552

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

theorem Formalism.DworkPowerSeriesWeights.bnx_pow_reduce (l d x : ℕ) (hl : 1 ≤ l) : l ^ x ≡ l ^ (x % d) [MOD l ^ d - 1] := by sorry
