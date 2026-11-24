-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_not_four_dvd
-- name    : Formalism.FrobeniusOrbits.Group.not_four_dvd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:52:11.874031+00:00
-- url     : https://prove2.me/theorems/400eabaa-9ddd-4407-8f96-5fc29d0242af
-- title:
--   Group: not four dvd
-- statement:
--   The Group construction uses the not four dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L38-L44

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

theorem Formalism.FrobeniusOrbits.Group.not_four_dvd (x : ℤ) (hx : Odd x) : ¬ (4 : ℤ) ∣ x ^ 2 + 1 := by sorry
