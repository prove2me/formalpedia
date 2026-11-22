-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_proposition_3_6
-- name    : AehligSchwichtenberg2002V2.proposition_3_6
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:56:47.633459+00:00
-- url     : https://prove2.me/theorems/e7040f13-938e-403b-9e6d-b9da26e65b89
-- title:
--   Proposition 3.6 — Canonical forms of normal almost closed terms
-- statement:
--   A normal term whose free variables all have token type has a canonical outer form at each of the following types. A list-typed term is a list spine, a Boolean is $\mathsf{tt}$ or $\mathsf{ff}$, and a term of token type is a variable of token type.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Proposition 3.6. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Syntax

namespace AehligSchwichtenberg2002V2

theorem proposition_3_6 {Γ : Context} {t : Term}
    (hac : IsAlmostClosed t) (hnorm : IsNormal t) :
    (∀ τ : Ty, HasType Γ t (.list τ) → IsListTerm t) ∧
    (HasType Γ t .bool → t = .const .tt ∨ t = .const .ff) ∧
    (HasType Γ t .diamond → ∃ x : Var, x.ty = .diamond ∧ t = .var x) := by sorry

end AehligSchwichtenberg2002V2
