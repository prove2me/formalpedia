-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_no_faithful_recordBook
-- name    : APFPaper1.RecordBook.no_faithful_recordBook
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:17:24.263195+00:00
-- url     : https://prove2.me/theorems/6a628e68-c241-4d4d-a4be-0e6cb6047143
-- title:
--   Separated alternating triples admit no faithful commuting sharp map
-- statement:
--   The obstruction is conditional on the separating relation and the total-word multiplicative model. It does not construct physically separating data or exclude every classical invasive process model. The result concerns equality-faithfulness to the chosen E, not unasserted properties of a full source defender. Fix a supplied relation E on words at one context, and suppose E does not relate xzx to zxz. There is no map into a specified commutative semigroup that is multiplicative, sharp at x and z, and identifies exactly the pairs related by E. Faithfulness here is an equivalence between equality of mapped values and E. Source: Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.
-- source:
--   Theorems/Thm_APFPaper1_RecordBook_collapse.lean, declaration at line 55 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.

import Definitions.Def_APFPaper1_RecordBook
import Definitions.Def_APFPaper1_ContextualEquivalence
import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
open APFPaper1.Continuation

universe uC uF uM uX uV
variable {Context : Type uC} {Frag : Context → Context → Type uF}

theorem APFPaper1.RecordBook.no_faithful_recordBook {M : Type uM} [CommSemigroup M] {a : Context}
    (E : Word Frag a a → Word Frag a a → Prop) {x z : Frag a a}
    (hsep : ¬ E (word3 x z x) (word3 z x z)) :
    ¬ ∃ rho : Word Frag a a → M,
        Multiplicative rho ∧ Sharp rho x ∧ Sharp rho z ∧ Faithful rho E := by sorry
