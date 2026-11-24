-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_zero
-- name    : Formalism.L2.FormalSeriesBounds.Contr.noConst_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:04.572616+00:00
-- url     : https://prove2.me/theorems/315ad82e-609a-419b-ad81-f350a2a4c3bb
-- title:
--   Contr: no Const zero
-- statement:
--   The Contr construction uses the no Const zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L49-L51

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
omit H

theorem Formalism.L2.FormalSeriesBounds.Contr.noConst_zero : NoConst (0 : B → MvPowerSeries Z k) := by sorry
