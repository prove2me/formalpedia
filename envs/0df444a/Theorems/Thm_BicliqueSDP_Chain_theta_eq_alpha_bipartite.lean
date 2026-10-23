-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_theta_eq_alpha_bipartite
-- name    : BicliqueSDP.Chain.theta_eq_alpha_bipartite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:33.302806+00:00
-- url     : https://prove2.me/theorems/3809a3a3-e7a1-48da-b730-f9af4b4a5895
-- title:
--   p. 12, after Eq. (25) — ϑ(G) = α(G) for every bipartite graph G
-- statement:
--   Let $G=(V_1\cup V_2,E)$ be a bipartite graph and $\alpha(G)$ the maximum of $|A|+|B|$ over its bipartite biindependent pairs $(A,B)$, that is, its stability number. Then the theta number of $G$, viewed as a graph on $V=V_1\cup V_2$, equals its stability number:
--   $$\vartheta(G)=\alpha(G).$$
--
--   The proof of Proposition 1.2 uses this to turn the bounds $4h_1(G)\le\vartheta(G)$ and $g_1(G)\le h_1(G)\,\vartheta(G)$ into bounds in terms of $\alpha(G)$.
--
--   **Formalization Note** The paper states this more generally for perfect graphs, citing Grötschel, Lovász and Schrijver; only the bipartite clause, which the paper uses, is formalized. $\vartheta$ is evaluated on `bipGraph E`, and $\alpha(G)$ is the paper's maximum over biindependent pairs.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, p. 12, the sentence after Eq. (25)

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- p. 12, after Eq. (25): `ϑ(G) = α(G)` if `G` is bipartite. -/
theorem theta_eq_alpha_bipartite {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1]
    [DecidableEq V2] (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    theta (bipGraph E) = alpha E := by sorry

end BicliqueSDP.Chain
