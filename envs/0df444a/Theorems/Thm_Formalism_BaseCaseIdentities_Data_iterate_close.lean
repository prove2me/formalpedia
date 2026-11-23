-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_iterate_close
-- name    : Formalism.BaseCaseIdentities.Data.iterate_close
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:53.839551+00:00
-- url     : https://prove2.me/theorems/cb15d69f-151e-4d37-a504-31629d23f544
-- title:
--   Data: iterate close
-- statement:
--   The Data construction uses the iterate close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L167-L176

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
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem Formalism.BaseCaseIdentities.Data.iterate_close {a b : C → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) ((D.Psi)^[n] a c - (D.Psi)^[n] b c) := by sorry
