-- Prove2me | Theorems.Thm_Formalism_D5_ne_of_val
-- name    : Formalism.D5.ne_of_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:29.208815+00:00
-- url     : https://prove2.me/theorems/a6c6cb46-7cc8-42db-bbaf-ed58caec9346
-- title:
--   D5: ne of val
-- statement:
--   The D5 construction uses the ne of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L162-L164

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

theorem Formalism.D5.ne_of_val {ψ φ : AddChar (E0 × H) ℂ} (g : E0 × H) (h : ψ g ≠ φ g) : ψ ≠ φ := by sorry
