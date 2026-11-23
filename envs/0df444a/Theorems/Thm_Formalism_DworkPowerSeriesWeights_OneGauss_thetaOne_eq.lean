-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_thetaOne_eq
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.thetaOne_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:21.332514+00:00
-- url     : https://prove2.me/theorems/54795128-703b-4716-ab18-0a4ef2aeb1cb
-- title:
--   One Gauss: theta One eq
-- statement:
--   The One Gauss construction uses the theta One eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L98-L102

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

theorem Formalism.DworkPowerSeriesWeights.OneGauss.thetaOne_eq (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    thetaOne g U sgn ep be = MvPowerSeries.subst g U *
      _root_.Formalism.DworkPowerSeriesWeights.mvExp (expo (fun x => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) sgn ep be) := by sorry
