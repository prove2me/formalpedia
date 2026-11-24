-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Group_ind
-- name    : Formalism.FrobeniusOrbits.Group.ind
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:53:05.179702+00:00
-- url     : https://prove2.me/theorems/da3f8ed5-3496-4978-a527-09db9682d4a9
-- title:
--   Group: ind
-- statement:
--   The Group construction uses the ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/CoprimeTwoPow.lean#L46-L66

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

theorem Formalism.FrobeniusOrbits.Group.ind (l : ℤ) (hl : Odd l) (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    ((2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ M ∣ l - 1 ∨ (2 : ℤ) ^ M ∣ l + 1) := by sorry
