-- Prove2me | Theorems.Thm_Formalism_HC_Der_tauN_zO
-- name    : Formalism.HC.Der.tauN_zO
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:24.032887+00:00
-- url     : https://prove2.me/theorems/1005ca67-596a-4ea4-9e6b-2f34e3fbc018
-- title:
--   Der: tau N z O
-- statement:
--   The Der construction uses the tau N z O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L67-L72

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
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
variable (N : ℕ) [NeZero N]

theorem Formalism.HC.Der.tauN_zO (u : (ZMod N)ˣ) : tauN N u • zO N = zO N ^ (u : ZMod N).val := by sorry
