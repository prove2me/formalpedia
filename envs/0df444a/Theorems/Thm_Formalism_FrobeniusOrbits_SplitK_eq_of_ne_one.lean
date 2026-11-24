-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_eq_of_ne_one
-- name    : Formalism.FrobeniusOrbits.SplitK.eq_of_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:31.411801+00:00
-- url     : https://prove2.me/theorems/93a0a03f-6151-4e3c-a1bc-cc48ad7ca9e1
-- title:
--   Split K: eq of ne one
-- statement:
--   The Split K construction uses the eq of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L230-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean#L230-L233

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

theorem Formalism.FrobeniusOrbits.SplitK.eq_of_ne_one (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (σ τ : Kd b ≃ₐ[ℚ] Kd b) (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) : σ = τ := by sorry
