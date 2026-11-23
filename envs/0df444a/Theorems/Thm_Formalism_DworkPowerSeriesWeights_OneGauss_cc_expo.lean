-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_cc_expo
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.cc_expo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:15.2601+00:00
-- url     : https://prove2.me/theorems/a9c21d9b-0c79-450f-a4bb-6d2d69832da2
-- title:
--   One Gauss: cc expo
-- statement:
--   The One Gauss construction uses the cc expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L33-L42

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

theorem Formalism.DworkPowerSeriesWeights.OneGauss.cc_expo (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (expo v sgn ep be) = 0 := by sorry
