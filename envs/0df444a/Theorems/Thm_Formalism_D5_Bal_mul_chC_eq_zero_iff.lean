-- Prove2me | Theorems.Thm_Formalism_D5_Bal_mul_chC_eq_zero_iff
-- name    : Formalism.D5.Bal.mul_chC_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:24.660947+00:00
-- url     : https://prove2.me/theorems/ab12f742-5fea-4d8a-85da-506ae736a47a
-- title:
--   Bal: mul ch C eq zero iff
-- statement:
--   The Bal construction uses the mul ch C eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ThickAverageProofs/Balance.lean#L114-L124

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

theorem Formalism.D5.Bal.mul_chC_eq_zero_iff (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) : ψ * Hs.chC = 0 ↔ ψ = Hs.chC := by sorry
