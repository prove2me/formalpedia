-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_coeff_sum_C_mul_X_pow
-- name    : Formalism.BaseCaseIdentities.coeff_sum_C_mul_X_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:32.872065+00:00
-- url     : https://prove2.me/theorems/9328a7cd-d1b8-4673-aabb-e5ac2598dd5d
-- title:
--   Base Case Identities: coeff sum C mul X pow
-- statement:
--   The Base Case Identities construction uses the coeff sum C mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L222-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L222-L228

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

theorem Formalism.BaseCaseIdentities.coeff_sum_C_mul_X_pow [Fintype Z] [DecidableEq Z] (y : Z → k) (M : ℕ) (B : Z →₀ ℕ) :
    coeff B (∑ d, C (y d) * X d ^ M : MvPowerSeries Z k)
      = ∑ d, if B = Finsupp.single d M then y d else 0 := by sorry
