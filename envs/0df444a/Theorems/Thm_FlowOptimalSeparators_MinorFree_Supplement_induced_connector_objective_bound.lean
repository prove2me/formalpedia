-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_Supplement_induced_connector_objective_bound
-- name    : FlowOptimalSeparators.MinorFree.Supplement.induced_connector_objective_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:01:28.585305+00:00
-- url     : https://prove2.me/theorems/83ddbb89-cff0-4fe3-b0bb-116ba6a7b514
-- title:
--   Lemma 5 — induced-minor-free connector objective bound
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $H$ be a finite graph and $G$ an $H$-induced-minor-free graph. Let $\lambda$ be any feasible solution of the optimization problem (11) over all wide connectors of $G$, with $\mu=\iota=1$: $0\le\lambda[C]\le1$ for every wide connector $C$, and the total weight of connectors rooted at each vertex is at most $1$. Then
--   $$F_{1,1}(\lambda)\ \le\ C\,\bigl(|V(H)|+|E(H)|\bigr).$$
--   Here $F_{1,1}(\lambda)=\|\lambda\|_1-\sum_{\{C,C'\},\,C\ne C'}\lambda[C]\lambda[C']\,H_{1,1}(p_C,p_{C'})$, where $p_C$ is the load vector of $C$ and $H_{1,1}(p,q)=\sum_v p[v]q[v]+\sum_{uv\in E(G)}(p[u]q[v]+p[v]q[u])$. Together with the progress bound of Lemma 2 it caps the number of rounds of Section 5's Cluster-FTRL.
--
--   Differences from the source:
--   - encoding: finite simple graphs H and G on arbitrary vertex sets → SimpleGraph (Fin a) and SimpleGraph (Fin n), with |V(H)| = a; reason: vertex relabelling preserves induced minors, paths, components and edge counts
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist (published WideConnector and FTRLRound); reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - reading: F1,1(λ) = O(|V(H)| + |E(H)|) → ∃ C > 0, chosen before H, G and λ, with F1,1(λ) ≤ C(|V(H)| + |E(H)|); reason: the optimization context and the proof on pp.21–22 give an upper bound with an absolute constant (121/(18c1)); c1 is not numeric, so no numeral is fixed
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 19, 21–22, Lemma 5, Eq. (27)

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree.Supplement

/-- Lemma 5, p.19 (proof pp.21-22), Eq. (27): one absolute `C > 0` such that every feasible
`λ` of (11) with `µ = ι = 1`, over every wide connector, has `F₁,₁(λ) ≤ C(|V(H)|+|E(H)|)`. -/
theorem induced_connector_objective_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a n : ℕ} (H : Graph a) (G : Graph n), InducedMinorFree H G →
        ∀ (lam : WideConnector G → ℝ), Feasible lam →
          objective G 1 1 lam ≤ C * ((a : ℝ) + edgeCount H) := by sorry

end FlowOptimalSeparators.MinorFree.Supplement
