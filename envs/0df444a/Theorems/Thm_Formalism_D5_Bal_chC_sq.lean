-- Prove2me | Theorems.Thm_Formalism_D5_Bal_chC_sq
-- name    : Formalism.D5.Bal.chC_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:42.722168+00:00
-- url     : https://prove2.me/theorems/a2cfe9e9-af1d-4f89-b016-17a72af89205
-- title:
--   Bal: ch C sq
-- statement:
--   The Bal construction uses the ch C sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L111-L112

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

theorem Formalism.D5.Bal.chC_sq (Hs : CycHost H) (g : E0 × H) : Hs.chC g * Hs.chC g = 1 := by sorry
