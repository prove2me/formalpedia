-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_pow_sub_frob
-- name    : Formalism.BaseCaseIdentities.hasWt_pow_sub_frob
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:24.111591+00:00
-- url     : https://prove2.me/theorems/87fef745-3669-471c-8385-42199167eff3
-- title:
--   Base Case Identities: has Wt pow sub frob
-- statement:
--   The Base Case Identities construction uses the has Wt pow sub frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L35-L47

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
variable {k : Type*} [Field k] {Z C : Type*}

theorem Formalism.BaseCaseIdentities.hasWt_pow_sub_frob [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {l e M : ℕ}
    (hl : l.Prime) (hv : v (l : k) = 1) (he : 1 ≤ e) (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w)
      ((∑ d, MvPowerSeries.C (x d) * X d ^ M) ^ (l ^ e)
        - frob (l ^ e) (∑ d, MvPowerSeries.C (x d) * X d ^ M)) := by sorry
