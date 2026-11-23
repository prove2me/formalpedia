-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
-- name    : Formalism.BaseCaseIdentities.Data.noConst_iterate
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:59.974035+00:00
-- url     : https://prove2.me/theorems/ad4959e1-e131-4af2-8474-6d16e4f445f4
-- title:
--   Data: no Const iterate
-- statement:
--   The Data construction uses the no Const iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L161-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L161-L165

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

theorem Formalism.BaseCaseIdentities.Data.noConst_iterate {t : C → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst ((D.Psi)^[n] t) := by sorry
