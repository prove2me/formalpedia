-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_oneLog
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.map_oneLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:01.813612+00:00
-- url     : https://prove2.me/theorems/5fa2553f-7b3b-46d5-b816-7cec03c5eade
-- title:
--   One Gauss: map one Log
-- statement:
--   The One Gauss construction uses the map one Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L87-L92

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

theorem Formalism.DworkPowerSeriesWeights.OneGauss.map_oneLog {F K : Type} [Field F] [Field K] (φ : F →+* K) {τ : Type} [DecidableEq τ]
    (l : ℕ) (x : τ) : MvPowerSeries.map φ (oneLog (K := F) l x) = oneLog l x := by sorry
