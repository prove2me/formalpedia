-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_frob_sum_X
-- name    : Formalism.BaseCaseIdentities.frob_sum_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:43.418935+00:00
-- url     : https://prove2.me/theorems/82db45b4-3ecb-4234-8ba7-c501b62f30c1
-- title:
--   Base Case Identities: frob sum X
-- statement:
--   The Base Case Identities construction uses the frob sum X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L230-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean#L230-L263

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

theorem Formalism.BaseCaseIdentities.frob_sum_X [Fintype Z] {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (x : Z → k) :
    frob N (∑ d, C (x d) * X d ^ M) = ∑ d, C (x d ^ N) * X d ^ (N * M) := by sorry
