-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_add_pow_sub_pow
-- name    : Formalism.BaseCaseIdentities.hasWt_add_pow_sub_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:28.2427+00:00
-- url     : https://prove2.me/theorems/01a7c190-5132-4185-9571-7d83561c60a0
-- title:
--   Base Case Identities: has Wt add pow sub pow
-- statement:
--   The Base Case Identities construction uses the has Wt add pow sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L171-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L171-L195

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

theorem Formalism.BaseCaseIdentities.hasWt_add_pow_sub_pow {l q : ℕ} (hv : v (l : k) = 1) (hq : 1 ≤ q)
    (hdiv : ∀ m, 0 < m → m < q → l ∣ q.choose m) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + ((q : ℝ) - 1) * wa + wb) ((a + b) ^ q - a ^ q - b ^ q) := by sorry
