-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
-- name    : Formalism.BaseCaseIdentities.HasWtG.mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:15.941242+00:00
-- url     : https://prove2.me/theorems/d3e8fdc2-12a8-43b7-b900-e94841ad7f50
-- title:
--   Has Wt G: mul
-- statement:
--   The Has Wt G construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean#L26-L37

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul

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

theorem Formalism.BaseCaseIdentities.HasWtG.mul {ω : (S →₀ ℕ) →+ ℝ} {w1 w2 : ℝ} {f g : MvPowerSeries S k}
    (hf : HasWtG v ω w1 f) (hg : HasWtG v ω w2 g) : HasWtG v ω (w1 + w2) (f * g) := by sorry
