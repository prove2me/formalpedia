-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_coprime_two_pow
-- name    : Formalism.FrobeniusOrbits.Group.coprime_two_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:22.302837+00:00
-- url     : https://prove2.me/theorems/2678c4f9-e9c3-476c-957b-90b104d063ac
-- title:
--   Group: coprime two pow
-- statement:
--   The Group construction uses the coprime two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L13-L16

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

theorem Formalism.FrobeniusOrbits.Group.coprime_two_pow (K : ℕ) {y : ℤ} (hy : Odd y) : IsCoprime ((2 : ℤ) ^ K) y := by sorry
