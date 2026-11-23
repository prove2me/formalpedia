-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_expo
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.map_expo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:18.904461+00:00
-- url     : https://prove2.me/theorems/5f238bfd-f468-40ea-b547-8c9d89cad2d2
-- title:
--   One Gauss: map expo
-- statement:
--   The One Gauss construction uses the map expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L62-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L62-L83

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
variable {K : Type} [Field K] {τ ι : Type} [Fintype τ]

theorem Formalism.DworkPowerSeriesWeights.OneGauss.map_expo {F : Type} [Field F] (φ : F →+* K) (v : τ → MvPowerSeries ι F)
    (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0) (sgn ep : F)
    (be : MvPowerSeries (ZMod 2) F) :
    MvPowerSeries.map φ (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.map φ (v x)) (φ sgn) (φ ep) (MvPowerSeries.map φ be) := by sorry
