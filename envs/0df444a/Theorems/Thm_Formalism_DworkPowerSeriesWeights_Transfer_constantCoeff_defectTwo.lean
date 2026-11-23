-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_defectTwo
-- name    : Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_defectTwo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:59.03432+00:00
-- url     : https://prove2.me/theorems/c34ac9b2-e58c-4502-846f-0b7ce2d55c97
-- title:
--   Transfer: constant Coeff defect Two
-- statement:
--   The Transfer construction uses the constant Coeff defect Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean#L115-L123

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

theorem Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_defectTwo {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by sorry
