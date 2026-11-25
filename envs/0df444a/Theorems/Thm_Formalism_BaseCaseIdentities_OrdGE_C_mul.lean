-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
-- name    : Formalism.BaseCaseIdentities.OrdGE.C_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:27.806803+00:00
-- url     : https://prove2.me/theorems/5e8af6e7-4436-4527-a701-d2a28542f279
-- title:
--   Ord GE: C mul
-- statement:
--   The Ord GE construction uses the C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L53-L56

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
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
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

theorem Formalism.BaseCaseIdentities.OrdGE.C_mul {n : ℕ} {f : MvPowerSeries Z k} (x : k) (hf : OrdGE n f) :
    OrdGE n (MvPowerSeries.C x * f) := by sorry
