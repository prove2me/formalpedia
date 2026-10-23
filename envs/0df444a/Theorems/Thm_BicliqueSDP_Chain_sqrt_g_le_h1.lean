-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_sqrt_g_le_h1
-- name    : BicliqueSDP.Chain.sqrt_g_le_h1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:29.384484+00:00
-- url     : https://prove2.me/theorems/c6219ad9-fe8e-4b33-8047-0ed36aa40575
-- title:
--   §3.3, p. 16 — ½√g(G) ≤ h₁(G)
-- statement:
--   For every bipartite graph $G=(V_1\cup V_2,E)$,
--   $$\tfrac12\sqrt{g(G)}\le h_1(G),$$
--   where $g(G)$ is the maximum of $|A|\cdot|B|$ over bipartite biindependent pairs and $h_1(G)$ is the semidefinite bound (9).
--
--   This is the second inequality of Proposition 1.2: the SDP bound $h_1$ dominates not only $h$ but also $\frac12\sqrt g$.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, §3.3, p. 16, "Proof of ½√g(G) ≤ h₁(G)"

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- §3.3, p. 16: `½√g(G) ≤ h₁(G)`. -/
theorem sqrt_g_le_h1 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    (1 / 2) * Real.sqrt (g E) ≤ h1 E := by sorry

end BicliqueSDP.Chain
