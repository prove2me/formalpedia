-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_update_le
-- name    : Formalism.DworkPowerSeriesWeights.bnx_update_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:24.981845+00:00
-- url     : https://prove2.me/theorems/198cb766-9886-4276-839a-d13b84c94d4d
-- title:
--   Dwork Power Series Weights: bnx update le
-- statement:
--   The Dwork Power Series Weights construction uses the bnx update le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L303-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L303-L310

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

theorem Formalism.DworkPowerSeriesWeights.bnx_update_le (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) :
    ∀ t, Function.update (⇑n) s j t ≤ n t := by sorry
