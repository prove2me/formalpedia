-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
-- name    : Formalism.FrobeniusOrbits.Group.key
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:46.221799+00:00
-- url     : https://prove2.me/theorems/474703dc-8c5b-4ab6-b35e-f1cbae2a533f
-- title:
--   Group: key
-- statement:
--   The Group construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L18-L36

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

theorem Formalism.FrobeniusOrbits.Group.key (x : ℤ) (hx : Odd x) (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℤ) ^ (K + 1) ∣ (x - 1) * (x + 1) ↔ (2 : ℤ) ^ K ∣ x - 1 ∨ (2 : ℤ) ^ K ∣ x + 1 := by sorry
