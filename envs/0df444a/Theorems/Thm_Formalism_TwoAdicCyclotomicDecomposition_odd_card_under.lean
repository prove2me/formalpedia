-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_card_under
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:20.241034+00:00
-- url     : https://prove2.me/theorems/e31c2fd7-29bd-4bf0-90f5-0541d640803e
-- title:
--   Two Adic Cyclotomic Decomposition: odd card under
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd card under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L18-L21

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_card_under {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by sorry
