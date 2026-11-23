-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_defectOne
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_defectOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:20.729254+00:00
-- url     : https://prove2.me/theorems/6462affa-d945-49cf-8a8a-4f2665abd169
-- title:
--   Transfer: map defect One
-- statement:
--   The Transfer construction uses the map defect One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L87-L94

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_defectOne (be : MvPowerSeries (ZMod d) F) : map φ (de1 be) = de1 (map φ be) := by sorry
