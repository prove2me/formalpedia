-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_frob_zero
-- name    : Formalism.BaseCaseIdentities.frob_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:06.305796+00:00
-- url     : https://prove2.me/theorems/eb70cfe5-2305-4a94-b106-cbe524338262
-- title:
--   Base Case Identities: frob zero
-- statement:
--   The Base Case Identities construction uses the frob zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L145-L149

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

theorem Formalism.BaseCaseIdentities.frob_zero {N : ℕ} (hN : 1 ≤ N) : frob N (0 : MvPowerSeries Z k) = 0 := by sorry
