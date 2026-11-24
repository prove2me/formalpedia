-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_sum_get
-- name    : Formalism.L2.FormalSeriesBounds.RF.sum_get
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:05.373305+00:00
-- url     : https://prove2.me/theorems/e45e0e3a-4ecf-42db-baf3-4877d7c438f8
-- title:
--   RF: sum get
-- statement:
--   The RF construction uses the sum get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L54-L59

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ}

theorem Formalism.L2.FormalSeriesBounds.RF.sum_get {α M : Type} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by sorry
