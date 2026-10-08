-- Prove2me | Theorems.Thm_ChinesePostman_Matching_zero_one_parity_solution_decomposes
-- name    : ChinesePostman.Matching.zero_one_parity_solution_decomposes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:56.909965+00:00
-- url     : https://prove2.me/theorems/8908641b-3199-484d-9be2-e81ef61ec2a3
-- title:
--   §3, p. 93 — decompose binary parity support into odd-node paths
-- statement:
--   Let $x_e\in\{0,1\}$ satisfy the parity equations in a finite loopless multigraph. Its support contains edge-disjoint edge-simple paths that pair every odd-degree node with exactly one other odd-degree node. If $M$ is that pairing and $P_{uv}$ its paths, then
--
--   $$
--   \forall\{u,v\}\in M,\quad E(P_{uv})\subseteq\{e:x_e=1\}.
--   $$
--
--   These paths expose a 1-matching that can be compared to the cost of $x$.
--
--   **Formalization Note** The paths need not partition the whole support: even-degree tours can remain after every odd node has been paired, as the paper explains.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 93, §3, path-decomposition paragraph, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 93: the support contains disjoint paths pairing all odd nodes;
even-degree tours may remain outside those paths. -/
theorem zero_one_parity_solution_decomposes
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (hx : IsParitySolution G x)
    (hx01 : ∀ e, x e ≤ 1) :
    ∃ f : V → V, IsOddPerfectMatching G f ∧
      ∃ P : V → List V × List E, MatchingPaths G f P ∧
        ∀ v ∈ oddNodes G, ∀ e ∈ (P v).2, x e = 1 := by sorry
end ChinesePostman.Matching
