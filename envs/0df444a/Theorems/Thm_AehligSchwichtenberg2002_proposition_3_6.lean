-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_proposition_3_6
-- name    : AehligSchwichtenberg2002.proposition_3_6
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:56:43.23806+00:00
-- url     : https://prove2.me/theorems/ca4f6a84-88c3-4e4d-b349-baf9d394ce06
-- title:
--   Proposition 3.6: Subject Reduction
-- statement:
--   If `Δ; Γ ⊢ r : ρ` and `r ↦ r'`, then `Δ; Γ' ⊢ r' : ρ` for a subcontext `Γ' ⊆ Γ` and `d(r') ≤ d(r)`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Proposition 3.6, p. 393.

import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem proposition_3_6 {Γ : Context} {t : Term}
    (hac : ∀ v ∈ Γ, v.ty = .diamond) (hnorm : IsNormal t) :
    (∀ τ : Ty, HasType Γ t (.list τ) → IsListTerm t) ∧
    (HasType Γ t .bool → t = .const .tt ∨ t = .const .ff) ∧
    (HasType Γ t .diamond → ∃ x : Var, x.ty = .diamond ∧ t = .var x) := by sorry

end AehligSchwichtenberg2002
