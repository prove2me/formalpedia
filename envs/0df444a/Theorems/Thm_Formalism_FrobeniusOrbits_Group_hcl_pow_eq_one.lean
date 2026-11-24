-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_hcl_pow_eq_one
-- name    : Formalism.FrobeniusOrbits.Group.hcl_pow_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:16.174003+00:00
-- url     : https://prove2.me/theorems/ad370808-e253-48ed-b9b6-301d702d5d47
-- title:
--   Group: hcl pow eq one
-- statement:
--   The Group construction uses the hcl pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L141-L154

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

theorem Formalism.FrobeniusOrbits.Group.hcl_pow_eq_one (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ) :
    (hcl e u) ^ k = 1 ↔ u ^ k = 1 ∨ u ^ k = -1 := by sorry
