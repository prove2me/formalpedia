-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_natCast_not_mem
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_natCast_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:26.972021+00:00
-- url     : https://prove2.me/theorems/ad3eaa88-f225-41d9-bddb-078c4aab0873
-- title:
--   Two Adic Cyclotomic Decomposition: odd nat Cast not mem
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd nat Cast not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L23-L29

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_natCast_not_mem {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] (m : ℕ) (hpm : ¬ p ∣ m) :
    (m : 𝓞 L) ∉ P := by sorry
