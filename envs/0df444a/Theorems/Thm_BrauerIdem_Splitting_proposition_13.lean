-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_proposition_13
-- name    : BrauerIdem.Splitting.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:17.467987+00:00
-- url     : https://prove2.me/theorems/cc50e113-d897-4587-b1a3-9bd67dae6fa4
-- title:
--   Proposition 13, pp. 8–9 — every solution c_t of ūX_n(ℓ) = −ū lies in K
-- statement:
--   Let $\ell<n$ and $n-\ell$ be even. If the unnormalised orbit-sum expansion $X_c=\sum_Oc_OD_O$ over $F=\mathbb Q(\delta)$ solves
--
--   $$
--   uX_c=-u,
--   $$
--
--   then every coefficient $c_O$ lies in $K$, the set of quotients $f/g$ with $f,g\in\mathbb Z[\delta]$, $g$ monic, and $\deg f\leq\deg g$. This controls specialization of the resulting splitting idempotent.
--
--   **Formalization Note** The equation is equivalent to the paper's equation with $\bar u$ by nonzero scalar rescaling. The orbit sums themselves are unnormalised.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, pp. 8–9, Proposition 13

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, Proposition 13, pp. 8–9. -/
theorem proposition_13 (n l : ℕ) (hl : l < n) (hpar : Even (n - l))
    (c : OrbitIdx n l → F)
    (hc : bmul (basis (uDiag n l)) (Xof c) = -basis (uDiag n l)) :
    ∀ O, c O ∈ Kring := by sorry

end BrauerIdem.Splitting
