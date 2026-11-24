-- Prove2me | Theorems.Thm_Formalism_HC_Der_tauN_root
-- name    : Formalism.HC.Der.tauN_root
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:21.74549+00:00
-- url     : https://prove2.me/theorems/750b7711-58ed-4f95-b922-78d405742b60
-- title:
--   Der: tau N root
-- statement:
--   The Der construction uses the tau N root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean#L38-L39

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
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
open Formalism.FrobeniusOrbits
variable (N : ℕ) [NeZero N]

theorem Formalism.HC.Der.tauN_root (u : (ZMod N)ˣ) (w : Cond.Cyc N) (hw : w ^ N = 1) : tauN N u w = w ^ (u : ZMod N).val := by sorry
