-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_mvExp
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.map_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:29.532216+00:00
-- url     : https://prove2.me/theorems/42ba7fc8-da03-4553-9019-060fd7e34fc1
-- title:
--   Transfer: map mv Exp
-- statement:
--   The Transfer construction uses the map mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L137-L140

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
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)

theorem Formalism.DworkPowerSeriesWeights.Transfer.map_mvExp {ι : Type} {f : MvPowerSeries ι F} (h : constantCoeff f = 0) :
    map φ (mvExp f) = mvExp (map φ f) := by sorry
