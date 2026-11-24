-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_smul_mem_of_eq
-- name    : Formalism.FrobeniusOrbits.SplitK.smul_mem_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:44.553798+00:00
-- url     : https://prove2.me/theorems/4f797cdc-dde0-4f97-b44f-e15163198732
-- title:
--   Split K: smul mem of eq
-- statement:
--   The Split K construction uses the smul mem of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L325-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L325-L330

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

theorem Formalism.FrobeniusOrbits.SplitK.smul_mem_of_eq (σ : Kd b ≃ₐ[ℚ] Kd b) (P : Ideal (𝓞 (Kd b))) (h : σ • P = P)
    (y : 𝓞 (Kd b)) (hy : y ∈ P) : σ • y ∈ P := by sorry
