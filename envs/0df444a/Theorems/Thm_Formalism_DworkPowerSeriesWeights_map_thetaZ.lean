-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_thetaZ
-- name    : Formalism.DworkPowerSeriesWeights.map_thetaZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:24.761807+00:00
-- url     : https://prove2.me/theorems/c887d3c0-cc3c-445b-bee0-980d28e3ac5f
-- title:
--   Dwork Power Series Weights: map theta Z
-- statement:
--   The Dwork Power Series Weights construction uses the map theta Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L87-L104

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
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
open Formalism.IncomingBounds
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.map_thetaZ (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaZ g U ε be) =
      thetaZ (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ ε)
        (MvPowerSeries.map φ be) := by sorry
