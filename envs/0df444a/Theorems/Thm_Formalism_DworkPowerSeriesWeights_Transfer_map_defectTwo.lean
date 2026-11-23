-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_defectTwo
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_defectTwo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:58.678013+00:00
-- url     : https://prove2.me/theorems/4c8b4650-9e52-4a18-906b-81ec66cac405
-- title:
--   Transfer: map defect Two
-- statement:
--   The Transfer construction uses the map defect Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L96-L103

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_defectTwo (be : MvPowerSeries (ZMod d) F) : map φ (de2 be) = de2 (map φ be) := by sorry
