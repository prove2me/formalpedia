-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_sum_pow_sub
-- name    : Formalism.BaseCaseIdentities.hasWt_sum_pow_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:15.86337+00:00
-- url     : https://prove2.me/theorems/421755c0-1158-4dab-b756-49aff12935cc
-- title:
--   Base Case Identities: has Wt sum pow sub
-- statement:
--   The Base Case Identities construction uses the has Wt sum pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L204-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L204-L220

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

theorem Formalism.BaseCaseIdentities.hasWt_sum_pow_sub {ι : Type*} {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (_he : 1 ≤ e)
    (s : Finset ι) {F : ι → MvPowerSeries Z k} (h : ∀ i ∈ s, HasWt v r w (F i)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w) ((∑ i ∈ s, F i) ^ (l ^ e) - ∑ i ∈ s, (F i) ^ (l ^ e)) := by sorry
