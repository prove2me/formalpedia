-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_v_natCast_nonneg
-- name    : Formalism.BaseCaseIdentities.v_natCast_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:35.948795+00:00
-- url     : https://prove2.me/theorems/cba353f0-b7d2-4f2a-9a32-0c9069f25d39
-- title:
--   Base Case Identities: v nat Cast nonneg
-- statement:
--   The Base Case Identities construction uses the v nat Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L151-L157

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

theorem Formalism.BaseCaseIdentities.v_natCast_nonneg (v : AddValuation k (WithTop ℝ)) (n : ℕ) : 0 ≤ v (n : k) := by sorry
