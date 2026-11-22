-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxM_false
-- name    : Formalism.DworkPowerSeriesWeights.bnxM_false
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:38.695839+00:00
-- url     : https://prove2.me/theorems/28fe31ab-790e-4826-8915-072f94bc0dc7
-- title:
--   Dwork Power Series Weights: bnx M false
-- statement:
--   The Dwork Power Series Weights construction uses the bnx M false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L273-L276

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

theorem Formalism.DworkPowerSeriesWeights.bnxM_false (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (false, s) = k s := by sorry
