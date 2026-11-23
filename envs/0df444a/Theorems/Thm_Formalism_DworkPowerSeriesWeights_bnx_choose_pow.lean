-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_choose_pow
-- name    : Formalism.DworkPowerSeriesWeights.bnx_choose_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:36.148855+00:00
-- url     : https://prove2.me/theorems/75ad5795-2e96-487c-8b66-9cc8942fe77c
-- title:
--   Dwork Power Series Weights: bnx choose pow
-- statement:
--   The Dwork Power Series Weights construction uses the bnx choose pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L464-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L464-L543

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

theorem Formalism.DworkPowerSeriesWeights.bnx_choose_pow {l : ℕ} (hl : l.Prime) (e : ℕ) (he : 1 ≤ e) :
    0 < l ^ (e - 1) ∧ l ^ (e - 1) < l ^ e ∧ (l ^ e).choose (l ^ (e - 1)) ≠ 0 ∧
      ¬ l ^ 2 ∣ (l ^ e).choose (l ^ (e - 1)) := by sorry
