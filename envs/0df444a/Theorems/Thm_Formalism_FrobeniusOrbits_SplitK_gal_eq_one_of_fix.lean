-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_gal_eq_one_of_fix
-- name    : Formalism.FrobeniusOrbits.SplitK.gal_eq_one_of_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:33.166363+00:00
-- url     : https://prove2.me/theorems/0e9ac52b-7b4d-4669-af4c-2964b99d0f15
-- title:
--   Split K: gal eq one of fix
-- statement:
--   The Split K construction uses the gal eq one of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L88-L93

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

theorem Formalism.FrobeniusOrbits.SplitK.gal_eq_one_of_fix (σ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = bK b) : σ = 1 := by sorry
