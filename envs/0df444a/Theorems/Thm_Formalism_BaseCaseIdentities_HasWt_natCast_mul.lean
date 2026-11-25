-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_natCast_mul
-- name    : Formalism.BaseCaseIdentities.HasWt.natCast_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:30.907412+00:00
-- url     : https://prove2.me/theorems/fc43fe8d-8e82-4c99-972c-af1d15b6a191
-- title:
--   Has Wt: nat Cast mul
-- statement:
--   The Has Wt construction uses the nat Cast mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L159-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L159-L169

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

theorem Formalism.BaseCaseIdentities.HasWt.natCast_mul {l n : ℕ} (hv : v (l : k) = 1) (hd : l ∣ n) (hf : HasWt v r w f) :
    HasWt v r (1 + w) ((n : MvPowerSeries Z k) * f) := by sorry
