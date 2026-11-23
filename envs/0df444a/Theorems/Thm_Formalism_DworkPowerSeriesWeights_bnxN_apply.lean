-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxN_apply
-- name    : Formalism.DworkPowerSeriesWeights.bnxN_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:21.213931+00:00
-- url     : https://prove2.me/theorems/296e4326-94d3-4e69-8131-013c7040023e
-- title:
--   Dwork Power Series Weights: bnx N apply
-- statement:
--   The Dwork Power Series Weights construction uses the bnx N apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SwappedParitySeriesBinomialForm.lean#L204-L207

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

theorem Formalism.DworkPowerSeriesWeights.bnxN_apply (m : V2 d →₀ ℕ) (s : ZMod d) : bnxN m s = m (false, s) + m (true, s) := by sorry
