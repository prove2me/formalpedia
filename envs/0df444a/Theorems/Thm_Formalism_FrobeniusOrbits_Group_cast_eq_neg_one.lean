-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_neg_one
-- name    : Formalism.FrobeniusOrbits.Group.cast_eq_neg_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:52:42.23+00:00
-- url     : https://prove2.me/theorems/e64e6412-fe74-496d-ba07-51eb330f78b2
-- title:
--   Group: cast eq neg one
-- statement:
--   The Group construction uses the cast eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L74-L78

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

theorem Formalism.FrobeniusOrbits.Group.cast_eq_neg_one (m : ℕ) (z : ℤ) : (z : ZMod m) = -1 ↔ (m : ℤ) ∣ z + 1 := by sorry
