-- Prove2me | Theorems.Thm_Formalism_D5_thick_filter
-- name    : Formalism.D5.thick_filter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:36.088679+00:00
-- url     : https://prove2.me/theorems/a7aa21a9-4332-47b0-9164-3ad11e77bc56
-- title:
--   D5: thick filter
-- statement:
--   The D5 construction uses the thick filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L203-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L203-L210

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

theorem Formalism.D5.thick_filter (T2 : Finset H) (u0 t : H) :
    univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t) ∧ IsThickAt T2 u0 (cconj + g + topPl t))
      = T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by sorry
