-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_g1_le_alpha_mul_h1
-- name    : BicliqueSDP.Chain.g1_le_alpha_mul_h1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:29.203528+00:00
-- url     : https://prove2.me/theorems/1bead5d1-88f3-4c59-80ae-0cd99809a53c
-- title:
--   §3.3, p. 18 — g₁(G) ≤ α(G)·h₁(G)
-- statement:
--   For every bipartite graph $G=(V_1\cup V_2,E)$,
--   $$g_1(G)\le\alpha(G)\,h_1(G),$$
--   where $g_1$ and $h_1$ are the semidefinite bounds (8) and (9) and $\alpha(G)$ is the stability number.
--
--   Combined with $h_1(G)\le\frac14\alpha(G)$ this gives $g_1(G)\le\frac14\alpha(G)^2$, i.e. the last inequality $\frac12\sqrt{g_1(G)}\le\frac14\alpha(G)$ of Proposition 1.2.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, §3.3, p. 18, "Proof of g₁(G) ≤ α(G)h₁(G)"

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- §3.3, p. 18: `g₁(G) ≤ α(G) h₁(G)`. -/
theorem g1_le_alpha_mul_h1 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1]
    [DecidableEq V2] (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    g1 E ≤ alpha E * h1 E := by sorry

end BicliqueSDP.Chain
