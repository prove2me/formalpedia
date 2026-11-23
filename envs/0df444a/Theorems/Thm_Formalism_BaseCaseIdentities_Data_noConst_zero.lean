-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero
-- name    : Formalism.BaseCaseIdentities.Data.noConst_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:47.966167+00:00
-- url     : https://prove2.me/theorems/e4189318-c777-483f-9051-7d441406233a
-- title:
--   Data: no Const zero
-- statement:
--   The Data construction uses the no Const zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L180-L182

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

theorem Formalism.BaseCaseIdentities.Data.noConst_zero : NoConst (0 : C → MvPowerSeries Z k) := by sorry
