-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
-- name    : Formalism.BaseCaseIdentities.OrdGE.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:12.963803+00:00
-- url     : https://prove2.me/theorems/fc596dc2-5d94-44c8-8296-bf76fb3309c9
-- title:
--   Ord GE: sum
-- statement:
--   The Ord GE construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L35-L39

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

theorem Formalism.BaseCaseIdentities.OrdGE.sum {ι : Type*} {n : ℕ} (s : Finset ι) {f : ι → MvPowerSeries Z k}
    (hf : ∀ i ∈ s, OrdGE n (f i)) : OrdGE n (∑ i ∈ s, f i) := by sorry
