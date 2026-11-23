-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_pow_mod
-- name    : Formalism.DworkPowerSeriesWeights.bnx_pow_mod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:30.896395+00:00
-- url     : https://prove2.me/theorems/b6351c44-c34b-4906-a80d-b3483085781c
-- title:
--   Dwork Power Series Weights: bnx pow mod
-- statement:
--   The Dwork Power Series Weights construction uses the bnx pow mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L554-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L554-L579

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

theorem Formalism.DworkPowerSeriesWeights.bnx_pow_mod (l d x y : ℕ) (hl : 3 ≤ l) (hd : 1 ≤ d)
    (h : l ^ x ≡ l ^ y [MOD l ^ d - 1]) : x % d = y % d := by sorry
