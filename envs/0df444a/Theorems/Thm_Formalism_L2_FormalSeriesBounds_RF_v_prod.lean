-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_v_prod
-- name    : Formalism.L2.FormalSeriesBounds.RF.v_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:06.618194+00:00
-- url     : https://prove2.me/theorems/36beb767-2490-48b8-b409-c3432e1be5ef
-- title:
--   RF: v prod
-- statement:
--   The RF construction uses the v prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L19-L22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
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

theorem Formalism.L2.FormalSeriesBounds.RF.v_prod (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by sorry
