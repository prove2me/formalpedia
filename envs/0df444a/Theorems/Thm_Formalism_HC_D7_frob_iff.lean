-- Prove2me | Theorems.Thm_Formalism_HC_D7_frob_iff
-- name    : Formalism.HC.D7.frob_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:47.600397+00:00
-- url     : https://prove2.me/theorems/9c3d8134-7613-44c0-8f7a-99e6bc84579e
-- title:
--   D7: frob iff
-- statement:
--   The D7 construction uses the frob iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L374-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L374-L396

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
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH

theorem Formalism.HC.D7.frob_iff {p : ℕ} (hp : p % 2 = 1) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)) = (p : ZMod (2 ^ (e + 2) * q * d))) (g : FrobeniusOrbits.GG e) :
    (((g.1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧ ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
      ∃ v : (ZMod (2 ^ (e + 2)))ˣ, (v : ZMod (2 ^ (e + 2))) = (p : ZMod _) ∧ g.2 = hcl e v) ↔ g = art0 e hH u := by sorry
