-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_order_le_card
-- name    : Formalism.FrobeniusOrbits.Group.order_le_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:52:33.580789+00:00
-- url     : https://prove2.me/theorems/bcceea0e-9c01-4f5a-9941-273d833d5e7c
-- title:
--   Group: order le card
-- statement:
--   The Group construction uses the order le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L133-L139

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

theorem Formalism.FrobeniusOrbits.Group.order_le_card (e : ℕ) (x : HGrp e) : orderOf x ≤ 2 ^ e := by sorry
