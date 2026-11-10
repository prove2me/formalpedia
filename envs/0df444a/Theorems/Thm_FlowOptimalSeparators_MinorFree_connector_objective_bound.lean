-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_connector_objective_bound
-- name    : FlowOptimalSeparators.MinorFree.connector_objective_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:07.475068+00:00
-- url     : https://prove2.me/theorems/6f48ec16-4691-4dd0-84cc-5a6fd7d3cbaf
-- title:
--   Lemma 3 — minor-free connector objective bound
-- statement:
--   Let $h\ge3$ and let $G$ be $K_h$-minor-free. For every feasible connector vector $\lambda$ over all wide connectors, with $\mu=1$ and $\iota=0$,
--   $$F_{1,0}(\lambda)\le\frac{121h^2}{18c_0},\qquad c_0=\frac1{2500}.$$
--   This is the explicit upper bound obtained on p.19. It requires neither a maximizing vector nor attainment of an optimum and supplies the uniform obstruction used in Theorem 2.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist; reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - reading: F₁,₀(λ)=O(h²) → F₁,₀(λ)≤121h²/(18c₀), c₀=1/2500; reason: the optimization context and the proof on p.19 give an upper bound, rather than a two-sided absolute-value assertion
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 16, 19, Lemma 3, Eq. (24), explicit proof bound

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 3, p.16, with its explicit proof bound on p.19, (24).
The sum is over every wide connector, and there is no optimum-attainment assumption. -/
theorem connector_objective_bound {n : ℕ} (G : Graph n) (h : ℕ) (hh : 3 ≤ h)
    (hG : ExcludesClique G h) (lam : WideConnector G → ℝ) (hlam : Feasible lam) :
    objective G 1 0 lam ≤ 121 * (h : ℝ) ^ 2 / (18 * (1 / 2500 : ℝ)) := by sorry

end FlowOptimalSeparators.MinorFree
