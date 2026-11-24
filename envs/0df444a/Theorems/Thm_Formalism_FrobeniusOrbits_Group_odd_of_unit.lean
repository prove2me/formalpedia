-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_odd_of_unit
-- name    : Formalism.FrobeniusOrbits.Group.odd_of_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:52:22.223121+00:00
-- url     : https://prove2.me/theorems/7dc54c41-f915-453e-855a-cb39e2986a88
-- title:
--   Group: odd of unit
-- statement:
--   The Group construction uses the odd of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L156-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L156-L170

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

theorem Formalism.FrobeniusOrbits.Group.odd_of_unit (e : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) : Odd l := by sorry
