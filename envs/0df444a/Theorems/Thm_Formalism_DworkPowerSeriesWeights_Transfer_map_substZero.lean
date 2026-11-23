-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_substZero
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_substZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:36.901977+00:00
-- url     : https://prove2.me/theorems/f423b51d-bb66-404c-ac40-65660838ce84
-- title:
--   Transfer: map subst Zero
-- statement:
--   The Transfer construction uses the map subst Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L16-L17

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_substZero (s : ZMod d) : map φ (s0 (K := F) s) = s0 s := by sorry
