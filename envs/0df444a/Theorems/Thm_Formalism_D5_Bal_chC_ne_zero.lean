-- Prove2me | Theorems.Thm_Formalism_D5_Bal_chC_ne_zero
-- name    : Formalism.D5.Bal.chC_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:45:17.414403+00:00
-- url     : https://prove2.me/theorems/6d11d9fa-3146-4f4b-aa3b-d9f8a313337e
-- title:
--   Bal: ch C ne zero
-- statement:
--   The Bal construction uses the ch C ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L126-L131

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

theorem Formalism.D5.Bal.chC_ne_zero (Hs : CycHost H) : Hs.chC ≠ 0 := by sorry
