-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_dot_const
-- name    : Formalism.DworkPowerSeriesWeights.bnx_dot_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:33.008071+00:00
-- url     : https://prove2.me/theorems/6065f493-3ac9-4bbf-a841-bc60e7b9a820
-- title:
--   Dwork Power Series Weights: bnx dot const
-- statement:
--   The Dwork Power Series Weights construction uses the bnx dot const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L651-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L651-L659

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

theorem Formalism.DworkPowerSeriesWeights.bnx_dot_const {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (n.degree : ℝ) * c := by sorry
