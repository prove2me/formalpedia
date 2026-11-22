-- Prove2me | Theorems.Thm_Formalism_D5_zmod_two_one_ne_zero
-- name    : Formalism.D5.zmod_two_one_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:02.998985+00:00
-- url     : https://prove2.me/theorems/3d8e406f-5933-48a4-aeac-6bff0c613ee0
-- title:
--   D5: zmod two one ne zero
-- statement:
--   The D5 construction uses the zmod two one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L23-L24

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.D5.zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by sorry
