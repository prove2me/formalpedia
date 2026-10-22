-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_unique_solution
-- name    : BrauerIdem.Splitting.unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:07.303758+00:00
-- url     : https://prove2.me/theorems/faf95b34-475b-411d-a88a-281f0c895dd0
-- title:
--   §3, p. 8, (5)–(6) — the linear equations in the c_t given by ūX_n(ℓ) are independent: X ↦ ūX is injective on orbit sums
-- statement:
--   Let $\ell<n$ and $n-\ell$ be even. Write $D_O$ for the unnormalised sum of diagrams in a simultaneous $\mathfrak S_n$-orbit with at most $\ell$ propagating lines, and set $X_c=\sum_Oc_OD_O$ over $F=\mathbb Q(\delta)$. If two coefficient families $c,c'$ have the same left product by $u$,
--
--   $$
--   uX_c=uX_{c'},
--   $$
--
--   then $c=c'$. Thus the resulting diagram equations are linearly independent, and in particular $uX=-u$ has at most one orbit-sum solution. This is the uniqueness supplied by the nonsingular system (6).
--
--   **Formalization Note** The equation uses the unnormalised cup diagram $u$; multiplication by the nonzero scalar $\delta^{-(n-\ell)/2}$ gives the paper's equation with $\bar u$. The parity condition is explicit.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 8, §3, equation (6) and following paragraph

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, §3, p. 8, equation (6) and the paragraph below it. -/
theorem unique_solution (n l : ℕ) (hl : l < n) (hpar : Even (n - l))
    (c c' : OrbitIdx n l → F)
    (h : bmul (basis (uDiag n l)) (Xof c) =
      bmul (basis (uDiag n l)) (Xof c')) :
    c = c' := by sorry

end BrauerIdem.Splitting
