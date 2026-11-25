-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_pow
-- name    : Formalism.BaseCaseIdentities.HasWtG.pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:37.449798+00:00
-- url     : https://prove2.me/theorems/0a50be98-867c-4519-9312-5d2088f463d5
-- title:
--   Has Wt G: pow
-- statement:
--   The Has Wt G construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L46-L54

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow

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
variable {k : Type*} [Field k] {S : Type*} {v : AddValuation k (WithTop ℝ)}

theorem Formalism.BaseCaseIdentities.HasWtG.pow {ω : (S →₀ ℕ) →+ ℝ} {w : ℝ} {f : MvPowerSeries S k}
    (hf : HasWtG v ω w f) (n : ℕ) : HasWtG v ω ((n : ℝ) * w) (f ^ n) := by sorry
