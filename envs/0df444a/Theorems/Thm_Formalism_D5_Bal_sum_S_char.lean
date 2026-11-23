-- Prove2me | Theorems.Thm_Formalism_D5_Bal_sum_S_char
-- name    : Formalism.D5.Bal.sum_S_char
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:25.884575+00:00
-- url     : https://prove2.me/theorems/19083fa3-c57d-47ab-9301-4c0ab3fba1a6
-- title:
--   Bal: sum S char
-- statement:
--   The Bal construction uses the sum S char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L147-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L147-L173

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.D5.Bal.sum_S_char (Hs : CycHost H) (t : H) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g)
      = if ψ = Hs.chC then -((PhiSet (H := H)).card : ℂ) else 0 := by sorry
