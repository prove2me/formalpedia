-- Prove2me | Theorems.Thm_CondBasedProd_hjb_well_posed
-- name    : CondBasedProd.hjb_well_posed
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:33.74172+00:00
-- url     : https://prove2.me/theorems/a60de9e3-8ff2-4f33-806d-0073ce5890ea
-- title:
--   HJB well-posedness, p.10: the system (2) has exactly one solution (corrected: $\partial_tJ(\xi,t)=r(0)$)
-- statement:
--   Let the model satisfy the standing assumptions and let $\lambda\ge0$. The HJB system
--   $$
--   \partial_tJ(x,t)=\max_{s\in\mathcal S}\bigl[r(s)-\lambda f(s)\bigl(J(x,t)-J(x+1,t)\bigr)\bigr]\ (x<\xi),\quad \partial_tJ(\xi,t)=r(0),\quad J(x,0)=-c_m(x)
--   $$
--   has a solution, and any two solutions agree on $x\le\xi$, $t\ge0$.
--
--   The source obtains existence from Theorem III of Bremaud (1980), using continuity and boundedness of $f$ and $r$ and compactness of $\mathcal S$. Together with the next milestone, uniqueness makes "$J^*_\lambda$ is the solution of (2)" a statement with a definite meaning.
--
--   Differences from the source:
--   - correction: (2) at x = ξ: ∂_t J*_λ(ξ,t) = 0 → ∂_t J*_λ(ξ,t) = r(0); reason: under (1) the failed system runs at s = 0 and earns r(0), so J*_λ(ξ,t) = r(0) t − c_m(ξ); with S = [0,1], r(s) = s − 2, f(s) = s, ξ = 1 the printed branch fails at x = ξ. Same when r(0) = 0
--   - generalization: "there exists a solution to (2)" → existence and uniqueness on x ≤ ξ, t ≥ 0; reason: Lemma 1 says "the solution"; the existence clause is the printed claim
--   - reading: failure level ξ ∈ ℕ (p.8; whether 0 ∈ ℕ is not said) → ξ : ℕ, with ξ = 0 allowed; reason: the inclusive reading; ξ = 0 is the one-level failed system and every other instance is unaffected
--   - encoding: t ∈ [0,T] and backward time k ∈ [t,0] (pp.9–10) → every t ≥ 0; the process runs in elapsed time v = t − k; reason: T plays no role in J*_λ(x,t), so every T is covered; same instances
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, Lemma 1 and following paragraph, display (2), p.10

import Mathlib
import Definitions.Def_CondBasedProd_IsHJBSolution

namespace CondBasedProd

/-- **HJB well-posedness** (Drent, Drent & Arts, arXiv:2308.07507v2, p.10, citing Bremaud 1980,
Theorem III): for `λ ≥ 0` the system (2), with the second branch corrected to `r(0)`, has a solution
on `x ≤ ξ`, `t ≥ 0`, and only one there.

**Formalization Note.** Uniqueness is on `x ≤ ξ`, `t ≥ 0`, the only place the system constrains `J`. -/
theorem hjb_well_posed (M : Model) (lam : ℝ) (hlam : 0 ≤ lam) : (∃ J, IsHJBSolution M lam J) ∧ ∀ J J', IsHJBSolution M lam J → IsHJBSolution M lam J' → ∀ x ≤ M.ξ, ∀ t, 0 ≤ t → J x t = J' x t := by sorry

end CondBasedProd
