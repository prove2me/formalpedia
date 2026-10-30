-- Prove2me | Theorems.Thm_ABHS2004_proposition_2_13
-- name    : ABHS2004.proposition_2_13
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:50.189013+00:00
-- url     : https://prove2.me/theorems/49839b16-26ee-4654-82f5-a18c8380df60
-- title:
--   Proposition 2.13: Subject Reduction for the Affine Term Calculus
-- statement:
--   If `Δ; Γ ⊢ M : ρ` and `M ↦ M'`, then `Δ; Γ' ⊢ M' : ρ` for a subcontext `Γ' ⊆ Γ`, preserving both types and the separation between passive (`Δ`) and linear (`Γ`) free variables.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Proposition 2.13, p. 11.

import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem proposition_2_13 {w : Term} {τ : Ty}
    (ht : HasType w τ) (hac : IsAlmostClosed w) (hnorm : IsNormal w) :
    HasCanonicalNormalForm τ w := by sorry

end ABHS2004
