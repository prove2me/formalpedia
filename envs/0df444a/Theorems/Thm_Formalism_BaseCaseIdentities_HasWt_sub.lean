-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sub
-- name    : Formalism.BaseCaseIdentities.HasWt.sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:04.005662+00:00
-- url     : https://prove2.me/theorems/d26d97e4-91a0-566d-afe0-136b319227a3
-- title:
--   Has Wt: sub
-- statement:
--   The Has Wt construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L42-L43

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
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
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}

theorem Formalism.BaseCaseIdentities.HasWt.sub (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f - g) := by sorry
