-- Prove2me | Theorems.Thm_Formalism_HC_D7_exists_sign
-- name    : Formalism.HC.D7.exists_sign
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:18.166418+00:00
-- url     : https://prove2.me/theorems/97ccc70c-972e-4b63-945f-3ad7e88dda7f
-- title:
--   D7: exists sign
-- statement:
--   The D7 construction uses the exists sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L24-L37

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.HC.D7.exists_sign {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ) :
    ∃ b : ℕ, Nat.Coprime b p ∧ jacobiSym (b : ℤ) p = (s : ℤ) := by sorry
