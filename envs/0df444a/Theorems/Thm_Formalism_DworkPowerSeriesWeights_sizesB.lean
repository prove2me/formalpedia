-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sizesB
-- name    : Formalism.DworkPowerSeriesWeights.sizesB
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:17.078813+00:00
-- url     : https://prove2.me/theorems/b1c6a050-3f55-4ab8-bbce-1b7d30d70d9d
-- title:
--   Dwork Power Series Weights: sizes B
-- statement:
--   The Dwork Power Series Weights construction uses the sizes B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/FinalB.lean#L102-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/FinalB.lean#L102-L131

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights

theorem Formalism.DworkPowerSeriesWeights.sizesB : SizesB := by sorry
