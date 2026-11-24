-- Prove2me | Theorems.Thm_Formalism_HC_Der_sq_odd_pow
-- name    : Formalism.HC.Der.sq_odd_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:46.01234+00:00
-- url     : https://prove2.me/theorems/cba1debd-aefa-449a-a1bd-06685451020c
-- title:
--   Der: sq odd pow
-- statement:
--   The Der construction uses the sq odd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L42-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L42-L86

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

theorem Formalism.HC.Der.sq_odd_pow {d : ℤ} {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hj : jacobiSym (-d) l = 1) (k : ℕ) :
    ∃ s : ℤ, (l : ℤ) ^ (k + 1) ∣ s ^ 2 + d := by sorry
