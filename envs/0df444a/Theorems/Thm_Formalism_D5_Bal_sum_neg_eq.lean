-- Prove2me | Theorems.Thm_Formalism_D5_Bal_sum_neg_eq
-- name    : Formalism.D5.Bal.sum_neg_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:35.602583+00:00
-- url     : https://prove2.me/theorems/297a1505-2e31-417b-b9e8-78ad413e8a2f
-- title:
--   Bal: sum neg eq
-- statement:
--   The Bal construction uses the sum neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L133-L133

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

theorem Formalism.D5.Bal.sum_neg_eq (F : E0 × H → ℂ) : ∑ g : E0 × H, F (-g) = ∑ g, F g := by sorry
