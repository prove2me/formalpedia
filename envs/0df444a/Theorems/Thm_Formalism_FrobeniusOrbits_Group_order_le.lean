-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_order_le
-- name    : Formalism.FrobeniusOrbits.Group.order_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:52.035074+00:00
-- url     : https://prove2.me/theorems/a01b151a-277f-402e-8352-e66907447a6b
-- title:
--   Group: order le
-- statement:
--   The Group construction uses the order le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L108-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L108-L131

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group

theorem Formalism.FrobeniusOrbits.Group.order_le (e : ℕ) (x : HGrp e) (j : ℕ) : orderOf x ≤ 2 ^ j ↔ x ^ (2 ^ j) = 1 := by sorry
