-- Prove2me | Theorems.Thm_ABHS2004V2_corollary_4_8
-- name    : ABHS2004V2.corollary_4_8
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:21:59.795322+00:00
-- url     : https://prove2.me/theorems/b8d1e44a-0e4d-4f72-ba2e-b47c5fd701e6
-- title:
--   Corollary 4.8 — Underivability of token creation and duplication
-- statement:
--   Falsity does not imply a token, and one token does not imply a tensor of two tokens. The displayed weak-conjunction elimination scheme is not derivable uniformly over well-formed formulas.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Corollary 4.8. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_Realizability

namespace ABHS2004V2

/-- Corollary 4.8. The system proves neither token creation from falsity nor token
duplication. The displayed weak-conjunction elimination scheme is not uniformly
provable over well-formed formulas. -/
theorem corollary_4_8 :
    ¬ ClosedProvable (.imp Formula.bot Formula.lozenge) ∧
    ¬ ClosedProvable (.imp Formula.lozenge (.tensor Formula.lozenge Formula.lozenge)) ∧
    ¬ (∀ A B C : Formula,
        A.WellFormed → B.WellFormed → C.WellFormed →
        ClosedProvable (.imp (.imp A (.imp B C)) (.imp (.conj A B) C))) := by sorry

end ABHS2004V2
