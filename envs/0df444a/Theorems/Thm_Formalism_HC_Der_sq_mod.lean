-- Prove2me | Theorems.Thm_Formalism_HC_Der_sq_mod
-- name    : Formalism.HC.Der.sq_mod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:13.436418+00:00
-- url     : https://prove2.me/theorems/d38eb45b-10e2-4556-b9ea-5d83e90651c5
-- title:
--   Der: sq mod
-- statement:
--   The Der construction uses the sq mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L88-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L88-L117

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.HC.Der.sq_mod {d : ℤ} (hd : d % 8 = 7) (m : ℕ) (hm0 : m ≠ 0)
    (hm : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ m → jacobiSym (-d) l = 1) : ∃ s : ℤ, (m : ℤ) ∣ s ^ 2 + d := by sorry
