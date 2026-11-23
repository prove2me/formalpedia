-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_unipotent_weight_bound
-- name    : Formalism.DworkPowerSeriesWeights.unipotent_weight_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:34.362253+00:00
-- url     : https://prove2.me/theorems/fb38f645-1f48-4e2e-b65e-ce26e37cc718
-- title:
--   Dwork Power Series Weights: unipotent weight bound
-- statement:
--   The Dwork Power Series Weights construction uses the unipotent weight bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/WeightsAddOverOrbitsLogLoss.lean#L16-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/WeightsAddOverOrbitsLogLoss.lean#L16-L58

import Definitions.Def_Formalism_GaussJetBounds_StatementO
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
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
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.unipotent_weight_bound : UWt.{u, v, w} := by sorry
