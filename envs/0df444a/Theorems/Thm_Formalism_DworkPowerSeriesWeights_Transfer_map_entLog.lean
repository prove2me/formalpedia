-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_entLog
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_entLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:32.824795+00:00
-- url     : https://prove2.me/theorems/a3928991-3971-4d98-aea5-917e07d27eeb
-- title:
--   Transfer: map ent Log
-- statement:
--   The Transfer construction uses the map ent Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L75-L83

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_entLog {N0 N1 : ℕ} (l : ℕ) (x : ZV d N0 N1) :
    map φ (entLog (K := F) l x) = entLog l x := by sorry
