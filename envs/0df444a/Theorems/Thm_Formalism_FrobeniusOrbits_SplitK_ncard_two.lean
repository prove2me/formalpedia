-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ncard_two
-- name    : Formalism.FrobeniusOrbits.SplitK.ncard_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:08.234314+00:00
-- url     : https://prove2.me/theorems/524ba7a7-558c-47fc-a08a-95e43b5d7b8f
-- title:
--   Split K: ncard two
-- statement:
--   The Split K construction uses the ncard two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L290-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L290-L323

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
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
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}

theorem Formalism.FrobeniusOrbits.SplitK.ncard_two (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : Kd b ≃ₐ[ℚ] Kd b) (h : σ • P ≠ P) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 := by sorry
