-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
-- name    : Formalism.BaseCaseIdentities.OrdGE.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:19.982512+00:00
-- url     : https://prove2.me/theorems/ca490086-0666-4bd4-a6a0-0d78b018d39e
-- title:
--   Ord GE: neg
-- statement:
--   The Ord GE construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L26-L28

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

theorem Formalism.BaseCaseIdentities.OrdGE.neg {n : ℕ} {f : MvPowerSeries Z k} (hf : OrdGE n f) : OrdGE n (-f) := by sorry
