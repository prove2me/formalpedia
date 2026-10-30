-- Prove2me | Theorems.Thm_ABHS2004_corollary_4_8
-- name    : ABHS2004.corollary_4_8
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:36.838589+00:00
-- url     : https://prove2.me/theorems/1747f247-f7a7-44e1-b4c6-03f368f7bf80
-- title:
--   Corollary 4.8: Substitution Commutes with Program Extraction
-- statement:
--   Replacing a free object variable `x` by a term `t` in a derivation `M` commutes with program extraction: `⟦M[x := t]⟧ = ⟦M⟧[x := t]`.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Corollary 4.8, p. 21.

import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem corollary_4_8 :
    ¬ ClosedProvable (.imp Formula.bot Formula.lozenge) ∧
    ¬ ClosedProvable (.imp Formula.lozenge (.tensor Formula.lozenge Formula.lozenge)) ∧
    ¬ (∀ A B C : Formula,
        ClosedProvable (.imp (.imp A (.imp B C)) (.imp (.conj A B) C))) := by sorry

end ABHS2004
