-- Prove2me | Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym
-- name    : Formalism.HC.D7.artinMap_second_eq_jacobiSym
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:09:50.957445+00:00
-- url     : https://prove2.me/theorems/ca8b0f25-3154-4bd9-a30e-5cf1a6a6dee4
-- title:
--   D7: artin Map second eq jacobi Sym
-- statement:
--   The D7 construction uses the artin Map second eq jacobi Sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean#L129-L132

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HC.D7
variable (φ : Frame) (hinj : Function.Injective φ.h)
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)

theorem Formalism.HC.D7.artinMap_second_eq_jacobiSym (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) :
    (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (2 ^ (e + 2) * q * d)).val : ℕ) : ℤ) d := by sorry
