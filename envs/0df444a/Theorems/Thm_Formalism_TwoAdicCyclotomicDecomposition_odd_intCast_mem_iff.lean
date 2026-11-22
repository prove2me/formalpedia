-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_intCast_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:04.437195+00:00
-- url     : https://prove2.me/theorems/0204c0df-c6a8-4ed1-ad3f-12a98b814b67
-- title:
--   Two Adic Cyclotomic Decomposition: odd int Cast mem iff
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd int Cast mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L12-L16

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_intCast_mem_iff {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 L) ∈ P ↔ (p : ℤ) ∣ n := by sorry
