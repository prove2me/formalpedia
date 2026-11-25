-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_add_pow_sub
-- name    : Formalism.BaseCaseIdentities.hasWt_add_pow_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:42.034015+00:00
-- url     : https://prove2.me/theorems/49ec42e1-f780-4b66-b28b-3329bc3f14fc
-- title:
--   Base Case Identities: has Wt add pow sub
-- statement:
--   The Base Case Identities construction uses the has Wt add pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L197-L202

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

theorem Formalism.BaseCaseIdentities.hasWt_add_pow_sub {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + (((l ^ e : ℕ) : ℝ) - 1) * wa + wb)
      ((a + b) ^ (l ^ e) - a ^ (l ^ e) - b ^ (l ^ e)) := by sorry
