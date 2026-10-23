-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_h1_le_alpha
-- name    : BicliqueSDP.Chain.h1_le_alpha
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:38.330957+00:00
-- url     : https://prove2.me/theorems/5d05c384-e767-4a6b-aefa-b8e22f1bc8a7
-- title:
--   §3.3, p. 18 — h₁(G) ≤ ¼α(G)
-- statement:
--   For every bipartite graph $G=(V_1\cup V_2,E)$ with stability number $\alpha(G)$ (the maximum of $|A|+|B|$ over bipartite biindependent pairs),
--   $$h_1(G)\le\tfrac14\alpha(G).$$
--
--   Together with $g_1(G)\le\alpha(G)h_1(G)$ it yields the last inequality $\frac12\sqrt{g_1(G)}\le\frac14\alpha(G)$ of Proposition 1.2.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, §3.3, p. 18, "Proof of h₁(G) ≤ ¼α(G)"

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- §3.3, p. 18: `h₁(G) ≤ ¼α(G)`. -/
theorem h1_le_alpha {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    h1 E ≤ (1 / 4) * alpha E := by sorry

end BicliqueSDP.Chain
