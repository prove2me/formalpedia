-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_subst_expo
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.subst_expo
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:50.969707+00:00
-- url     : https://prove2.me/theorems/657aed03-4298-4414-88f5-d3ca0078d996
-- title:
--   One Gauss: subst expo
-- statement:
--   The One Gauss construction uses the subst expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L44-L60

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
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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

theorem Formalism.DworkPowerSeriesWeights.OneGauss.subst_expo {ι' : Type} {a : ι → MvPowerSeries ι' K} (hs : MvPowerSeries.HasSubst a)
    (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    MvPowerSeries.subst a (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.subst a (v x)) sgn ep be := by sorry
