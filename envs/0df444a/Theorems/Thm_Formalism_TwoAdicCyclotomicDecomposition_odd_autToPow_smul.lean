-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_autToPow_smul
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_autToPow_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:06:07.796427+00:00
-- url     : https://prove2.me/theorems/c5807132-926a-462b-ac8e-a99f63884859
-- title:
--   Two Adic Cyclotomic Decomposition: odd aut To Pow smul
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd aut To Pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L141-L146

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_autToPow_smul {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (σ : Gal(L/ℚ)) :
    σ • hζ.toInteger = hζ.toInteger ^ ((hζ.autToPow ℚ σ : ZMod (2 ^ n))).val := by sorry
