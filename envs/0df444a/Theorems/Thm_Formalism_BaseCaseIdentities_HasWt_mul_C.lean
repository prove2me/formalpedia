-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul_C
-- name    : Formalism.BaseCaseIdentities.HasWt.mul_C
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:15.63779+00:00
-- url     : https://prove2.me/theorems/135a99f4-9c50-4a69-9ee3-4a629cd1f32b
-- title:
--   Has Wt: mul C
-- statement:
--   The Has Wt construction uses the mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L80-L82

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

theorem Formalism.BaseCaseIdentities.HasWt.mul_C {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (f * C x) := by sorry
