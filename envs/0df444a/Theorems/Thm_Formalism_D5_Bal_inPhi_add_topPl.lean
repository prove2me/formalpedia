-- Prove2me | Theorems.Thm_Formalism_D5_Bal_inPhi_add_topPl
-- name    : Formalism.D5.Bal.inPhi_add_topPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:36.102697+00:00
-- url     : https://prove2.me/theorems/de8057f7-9113-4d7d-b09e-870e48411067
-- title:
--   Bal: in Phi add top Pl
-- statement:
--   The Bal construction uses the in Phi add top Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L24-L26

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

theorem Formalism.D5.Bal.inPhi_add_topPl (g : E0 × H) (t : H) : InPhi (g + topPl t) ↔ InPhi g := by sorry
