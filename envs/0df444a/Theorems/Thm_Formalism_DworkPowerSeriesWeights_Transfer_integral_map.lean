-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_integral_map
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.integral_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:58.710693+00:00
-- url     : https://prove2.me/theorems/50f89fa2-52e6-4251-9162-dcf2712ca934
-- title:
--   Transfer: integral map
-- statement:
--   The Transfer construction uses the integral map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L142-L146

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.integral_map (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {U : MvPowerSeries ι F}
    (h : Integral U) : Integral (map φ U) := by sorry
