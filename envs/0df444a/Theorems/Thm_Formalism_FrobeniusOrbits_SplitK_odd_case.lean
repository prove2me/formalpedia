-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_odd_case
-- name    : Formalism.FrobeniusOrbits.SplitK.odd_case
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:31.433081+00:00
-- url     : https://prove2.me/theorems/24a02dd3-753b-4e01-8269-21115a1dc921
-- title:
--   Split K: odd case
-- statement:
--   The Split K construction uses the odd case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L397-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L397-L486

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

theorem Formalism.FrobeniusOrbits.SplitK.odd_case (hd : d.Prime) (hb : b ^ 2 = -(d : L)) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : p ≠ d) (P : Ideal (𝓞 (Kd b))) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔ jacobiSym (-(d : ℤ)) p = 1 := by sorry
