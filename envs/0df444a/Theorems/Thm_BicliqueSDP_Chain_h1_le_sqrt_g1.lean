-- Prove2me | Theorems.Thm_BicliqueSDP_Chain_h1_le_sqrt_g1
-- name    : BicliqueSDP.Chain.h1_le_sqrt_g1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:33.895439+00:00
-- url     : https://prove2.me/theorems/7297c149-28bc-406f-924e-3074bd776044
-- title:
--   §3.3, pp. 16–17 — h₁(G) ≤ ½√g₁(G)
-- statement:
--   For every bipartite graph $G=(V_1\cup V_2,E)$, the two semidefinite bounds (8) and (9) satisfy
--   $$h_1(G)\le\tfrac12\sqrt{g_1(G)}.$$
--
--   This is the third inequality of Proposition 1.2, and the technically involved one: the paper compares it with the classical proof of $\mathrm{las}_1(G)\ge\vartheta(G)$ (Remark 3.8). The inequality can be strict, for instance for $K_{n,n}$ minus a perfect matching with $n\ge5$.
-- source:
--   Laurent, Polak, Vargas, Semidefinite approximations for bicliques and biindependent pairs, arXiv:2302.08886v2, §3.3, pp. 16–17, "Proof of h₁(G) ≤ ½√g₁(G)"

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

namespace BicliqueSDP.Chain

/-- §3.3, pp. 16–17: `h₁(G) ≤ ½√g₁(G)`. -/
theorem h1_le_sqrt_g1 {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) :
    h1 E ≤ (1 / 2) * Real.sqrt (g1 E) := by sorry

end BicliqueSDP.Chain
