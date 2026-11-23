-- Prove2me | Theorems.Thm_Formalism_D5_sum_H
-- name    : Formalism.D5.sum_H
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:30.864888+00:00
-- url     : https://prove2.me/theorems/dd3f8bbe-4ec1-45b5-af10-799cf87dc26e
-- title:
--   D5: sum H
-- statement:
--   The D5 construction uses the sum H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L53-L72

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
open Classical

theorem Formalism.D5.sum_H (ψ : AddChar (E0 × H) ℂ) :
    ∑ h : H, ψ ((0, 0), h) = if TrivH ψ then (Fintype.card H : ℂ) else 0 := by sorry
