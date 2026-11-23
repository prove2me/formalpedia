-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_thetaOne
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.map_thetaOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:06.483977+00:00
-- url     : https://prove2.me/theorems/70961eb2-00c7-419f-8420-929ccb2997e5
-- title:
--   One Gauss: map theta One
-- statement:
--   The One Gauss construction uses the map theta One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L104-L116

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
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
open Formalism.DworkPowerSeriesWeights.OneGauss
variable {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}

theorem Formalism.DworkPowerSeriesWeights.OneGauss.map_thetaOne {F : Type} [NormedField F] [CharZero F] (φ : F →+* K)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaOne g U sgn ep be) =
      thetaOne (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ sgn) (φ ep)
        (MvPowerSeries.map φ be) := by sorry
