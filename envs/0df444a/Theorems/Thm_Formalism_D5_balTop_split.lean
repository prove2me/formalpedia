-- Prove2me | Theorems.Thm_Formalism_D5_balTop_split
-- name    : Formalism.D5.balTop_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:21.319885+00:00
-- url     : https://prove2.me/theorems/ee518eef-56e9-4273-a6e8-b5e411c63ad4
-- title:
--   D5: bal Top split
-- statement:
--   The D5 construction uses the bal Top split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L244-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/ThickAverage.lean#L244-L264

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

theorem Formalism.D5.balTop_split {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 t : H) (j : Fin m) :
    balTop Hs (Nd.a t) t (Nd.w u0 j) = (thickZ Hs Nd u0 t j).re +
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt Nd.T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((Nd.w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.w u0 j (cconj + g + topPl t))).re := by sorry
