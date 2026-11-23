-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_single_add_single_eq
-- name    : Formalism.DworkPowerSeriesWeights.bnx_single_add_single_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:32.106476+00:00
-- url     : https://prove2.me/theorems/b6fef1a6-7134-4f6c-b0ce-2782ecb03940
-- title:
--   Dwork Power Series Weights: bnx single add single eq
-- statement:
--   The Dwork Power Series Weights construction uses the bnx single add single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L32-L42

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

theorem Formalism.DworkPowerSeriesWeights.bnx_single_add_single_eq {σ : Type*} {x y : σ} (hxy : x ≠ y) (r s i j : ℕ) :
    Finsupp.single x r + Finsupp.single y s = Finsupp.single x i + Finsupp.single y j ↔
      r = i ∧ s = j := by sorry
