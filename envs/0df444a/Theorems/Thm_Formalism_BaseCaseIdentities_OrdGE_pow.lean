-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
-- name    : Formalism.BaseCaseIdentities.OrdGE.pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:10.701169+00:00
-- url     : https://prove2.me/theorems/aa420d90-82fb-496a-a31a-b88b9f25c152
-- title:
--   Ord GE: pow
-- statement:
--   The Ord GE construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L58-L61

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

theorem Formalism.BaseCaseIdentities.OrdGE.pow {f : MvPowerSeries Z k} (hf : OrdGE 1 f) (n : ℕ) : OrdGE n (f ^ n) := by sorry
