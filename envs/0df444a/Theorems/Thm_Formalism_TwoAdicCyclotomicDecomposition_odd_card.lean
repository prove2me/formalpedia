-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:41.232259+00:00
-- url     : https://prove2.me/theorems/188e40bc-89c6-42eb-a5d8-332298d010c1
-- title:
--   Two Adic Cyclotomic Decomposition: odd card
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L221-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L221-L229

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_card (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (r : ℕ) [Fact r.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] :
    Nat.card (P.inertia Gal(L/ℚ)) = P.ramificationIdx ℤ := by sorry
