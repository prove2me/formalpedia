-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_substOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:22.368527+00:00
-- url     : https://prove2.me/theorems/ad44fc68-0f1c-4e7d-acc7-879b4719e49d
-- title:
--   Transfer: map subst One
-- statement:
--   The Transfer construction uses the map subst One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L18-L20

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_substOne (s : ZMod d) : map φ (s1 (K := F) s) = s1 s := by sorry
