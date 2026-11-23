-- Prove2me | Theorems.Thm_Formalism_D5_Bal_phiSet_card_ne_zero
-- name    : Formalism.D5.Bal.phiSet_card_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:47.6219+00:00
-- url     : https://prove2.me/theorems/20e7a61e-7abd-41c2-b3c4-17a8edc76a0a
-- title:
--   Bal: phi Set card ne zero
-- statement:
--   The Bal construction uses the phi Set card ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L91-L95

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

theorem Formalism.D5.Bal.phiSet_card_ne_zero : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by sorry
