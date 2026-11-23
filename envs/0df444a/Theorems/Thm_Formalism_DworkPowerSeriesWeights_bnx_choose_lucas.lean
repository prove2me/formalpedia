-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_choose_lucas
-- name    : Formalism.DworkPowerSeriesWeights.bnx_choose_lucas
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:10.261938+00:00
-- url     : https://prove2.me/theorems/9e5cf27d-27f1-4f52-bbd9-2defba093ad6
-- title:
--   Dwork Power Series Weights: bnx choose lucas
-- statement:
--   The Dwork Power Series Weights construction uses the bnx choose lucas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L431-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L431-L443

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

theorem Formalism.DworkPowerSeriesWeights.bnx_choose_lucas {l : ℕ} (hl : l.Prime) (c : ℕ) :
    ∀ a : ℕ, (l ^ a * c).choose (l ^ a) ≡ c [MOD l] := by sorry
