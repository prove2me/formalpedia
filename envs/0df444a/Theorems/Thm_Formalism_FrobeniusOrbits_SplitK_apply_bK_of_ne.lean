-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_apply_bK_of_ne
-- name    : Formalism.FrobeniusOrbits.SplitK.apply_bK_of_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:30.206421+00:00
-- url     : https://prove2.me/theorems/07b5dea6-e263-4124-af7b-97156bb4dd21
-- title:
--   Split K: apply b K of ne
-- statement:
--   The Split K construction uses the apply b K of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L224-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L224-L228

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

theorem Formalism.FrobeniusOrbits.SplitK.apply_bK_of_ne (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (ι : Kd b ≃ₐ[ℚ] Kd b) (hι : ι ≠ 1) :
    ι (bK b) = -bK b := by sorry
