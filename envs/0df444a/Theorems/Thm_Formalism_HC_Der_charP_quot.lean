-- Prove2me | Theorems.Thm_Formalism_HC_Der_charP_quot
-- name    : Formalism.HC.Der.charP_quot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:34.768301+00:00
-- url     : https://prove2.me/theorems/57daf61a-4b87-4175-98b1-7edc2cbb1f85
-- title:
--   Der: char P quot
-- statement:
--   The Der construction uses the char P quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean#L89-L96

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
variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]

theorem Formalism.HC.Der.charP_quot : CharP (𝓞 (Cond.Cyc N) ⧸ Q) l := by sorry
