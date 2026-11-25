-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_qs_sigma_lt_one
-- name    : Formalism.BaseCaseIdentities.Data.qs_sigma_lt_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:39.131194+00:00
-- url     : https://prove2.me/theorems/df36aaec-91b4-4282-85a9-4a3480c59831
-- title:
--   Data: qs sigma lt one
-- statement:
--   The Data construction uses the qs sigma lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/FixAll.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/FixAll.lean#L16-L31

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

theorem Formalism.BaseCaseIdentities.Data.qs_sigma_lt_one (s : ℕ) (hsK : s < D.K) : qnum D.l ^ s * sg D.l D.i < 1 := by sorry
