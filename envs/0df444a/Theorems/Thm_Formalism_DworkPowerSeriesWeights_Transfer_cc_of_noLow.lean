-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_of_noLow
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:25.93598+00:00
-- url     : https://prove2.me/theorems/d22bb683-d550-48d3-8c74-69f579df7216
-- title:
--   Transfer: cc of no Low
-- statement:
--   The Transfer construction uses the cc of no Low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L125-L129

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}
variable [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow {be : MvPowerSeries (ZMod d) F} (h : NoLowBidegree be) :
    constantCoeff be = 0 := by sorry
