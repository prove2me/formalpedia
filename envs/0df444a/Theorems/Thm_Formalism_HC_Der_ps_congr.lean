-- Prove2me | Theorems.Thm_Formalism_HC_Der_ps_congr
-- name    : Formalism.HC.Der.ps_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:40.041993+00:00
-- url     : https://prove2.me/theorems/54cad371-7d8e-4d35-975d-13e577b1bceb
-- title:
--   Der: ps congr
-- statement:
--   The Der construction uses the ps congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L181-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L181-L191

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
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.Der.ps_congr (u w : (ZMod H.condN)ˣ) (h : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) w) :
    (H.art u).1.1 = (H.art w).1.1 := by sorry
