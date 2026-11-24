-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_one
-- name    : Formalism.FrobeniusOrbits.Group.cast_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:19.036359+00:00
-- url     : https://prove2.me/theorems/2f528419-6c9b-467c-8d93-f6ff60b1fe3d
-- title:
--   Group: cast eq one
-- statement:
--   The Group construction uses the cast eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L68-L72

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

theorem Formalism.FrobeniusOrbits.Group.cast_eq_one (m : ℕ) (z : ℤ) : (z : ZMod m) = 1 ↔ (m : ℤ) ∣ z - 1 := by sorry
