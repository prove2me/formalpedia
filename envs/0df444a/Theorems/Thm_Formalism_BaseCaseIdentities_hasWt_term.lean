-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_term
-- name    : Formalism.BaseCaseIdentities.hasWt_term
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:10.425802+00:00
-- url     : https://prove2.me/theorems/51f7c4be-a820-4a78-a9e2-0069d879dabc
-- title:
--   Base Case Identities: has Wt term
-- statement:
--   The Base Case Identities construction uses the has Wt term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/ChainI.lean#L14-L33

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

theorem Formalism.BaseCaseIdentities.hasWt_term [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) (d : Z) :
    HasWt v r w (MvPowerSeries.C (x d) * X d ^ M) := by sorry
