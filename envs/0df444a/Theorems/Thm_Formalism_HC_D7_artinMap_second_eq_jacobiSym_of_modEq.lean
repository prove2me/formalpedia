-- Prove2me | Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
-- name    : Formalism.HC.D7.artinMap_second_eq_jacobiSym_of_modEq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:46.379851+00:00
-- url     : https://prove2.me/theorems/773a6358-fb2c-4d87-8fe1-b61992171135
-- title:
--   D7: artin Map second eq jacobi Sym of mod Eq
-- statement:
--   The D7 construction uses the artin Map second eq jacobi Sym of mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L181-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSymOfModEq.lean#L181-L186

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

theorem Formalism.HC.D7.artinMap_second_eq_jacobiSym_of_modEq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD d]) :
    (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) d := by sorry
