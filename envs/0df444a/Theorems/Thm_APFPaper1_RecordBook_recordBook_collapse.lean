-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_recordBook_collapse
-- name    : APFPaper1.RecordBook.recordBook_collapse
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:21:16.094301+00:00
-- url     : https://prove2.me/theorems/f8c1745c-8f07-42be-8258-12ae3343ff1a
-- title:
--   Sharp letters in a commuting word model collapse alternating triples
-- statement:
--   The map is total on words in this supplied model. The theorem isolates the commuting sharp-record calculation used in the Supplement; it does not encode the complete finite-tested defender with recovery maps, state weights or charging, nor establish that any physical interface distinguishes the two words. Suppose rho maps all words at one context into a commutative semigroup and sends every concatenation to multiplication. If the values of single letters x and z are idempotent, then rho assigns the same value to xzx and zxz. These are the only substantive algebraic premises of the result. Source: Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.
-- source:
--   Theorems/Thm_APFPaper1_RecordBook_collapse.lean, declaration at line 47 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.

import Definitions.Def_APFPaper1_RecordBook
import Definitions.Def_APFPaper1_ContextualEquivalence
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
open APFPaper1.RecordBook
open APFPaper1.Continuation

universe uC uF uM uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF}

theorem APFPaper1.RecordBook.recordBook_collapse {M : Type uM} [CommSemigroup M] {a : Context}
    {rho : Word Frag a a → M} (hmul : Multiplicative rho) {x z : Frag a a}
    (hx : Sharp rho x) (hz : Sharp rho z) :
    rho (word3 x z x) = rho (word3 z x z) := by sorry
