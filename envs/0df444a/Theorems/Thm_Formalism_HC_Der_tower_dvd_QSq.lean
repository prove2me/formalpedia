-- Prove2me | Theorems.Thm_Formalism_HC_Der_tower_dvd_QSq
-- name    : Formalism.HC.Der.tower_dvd_QSq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:15.237476+00:00
-- url     : https://prove2.me/theorems/f30cf0c5-0d3b-4b18-a717-0346899fe191
-- title:
--   Der: tower dvd QSq
-- statement:
--   The Der construction uses the tower dvd QSq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycGrp.lean#L153-L153

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

theorem Formalism.HC.Der.tower_dvd_QSq : 2 ^ (φ.e + 2) ∣ H.QS * H.q := by sorry
