-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_ram_ne_one
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_ram_ne_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:45.222038+00:00
-- url     : https://prove2.me/theorems/60794cc0-3256-4de9-8ea9-3f8beec86fef
-- title:
--   Two Adic Cyclotomic Decomposition: odd ram ne one
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd ram ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L231-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L231-L251

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

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_ram_ne_one {L : Type} [Field L] [NumberField L] (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] (x : L)
    (hx : x ^ 2 = ((-(r : ℤ) : ℤ) : L)) :
    P.ramificationIdx ℤ ≠ 1 := by sorry
