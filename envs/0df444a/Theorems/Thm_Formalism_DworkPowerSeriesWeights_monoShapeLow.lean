-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoShapeLow
-- name    : Formalism.DworkPowerSeriesWeights.monoShapeLow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:47.324505+00:00
-- url     : https://prove2.me/theorems/ffd6f1f7-1b07-454a-8e2c-b4e448a67747
-- title:
--   Dwork Power Series Weights: mono Shape Low
-- statement:
--   The Dwork Power Series Weights construction uses the mono Shape Low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/MonoShapeTop.lean#L85-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/MonoShapeTop.lean#L85-L117

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open Formalism Formalism.DworkPowerSeriesWeights

theorem Formalism.DworkPowerSeriesWeights.monoShapeLow : MonoShapeLow.{u} := by sorry
