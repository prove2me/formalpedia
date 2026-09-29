-- Prove2me | Theorems.Thm_ChvatalPolytopes_Separation_sum_le_indepNum_isFacet
-- name    : ChvatalPolytopes.Separation.sum_le_indepNum_isFacet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:19:01.959378+00:00
-- url     : https://prove2.me/theorems/ff04e451-4168-413b-add5-2d01ac9b15d2
-- title:
--   Theorem 4.2 — $\sum_u x_u\le\alpha(G)$ is a facet when the critical edges connect $V$
-- statement:
--   Let $G=(V,E)$ be a finite graph with stability number $\alpha(G)$, let $E^*$ be the set of its critical edges (edges $e$ with $\alpha(G-e)=\alpha(G)+1$) and $G^*=(V,E^*)$. If $G^*$ is connected, then the inequality
--   $$\sum_{u\in V}x_u\le\alpha(G)$$
--   is a facet of $P(G)$: every defining linear system of $P(G)$ contains a positive multiple of it.
--
--   The inequality $\sum_u x_u\le\alpha(G)$ is valid for every graph; the theorem gives a purely combinatorial condition under which no linear description of $P(G)$ can do without it. For $\alpha$-critical connected graphs $G^*=G$, which is how the theorem enters Corollary 4.3.
--
--   **Formalization Note** "Connected" is Mathlib's `Connected`, which includes that $V$ is nonempty; for $V=\emptyset$ the conclusion would be false (the empty system defines $P(G)$), so this is the right reading. $\alpha(G)$ is the natural number `indepNum`, cast to $\mathbb R$; "facet" is the mission's `IsFacet` (the paper's definition), with coefficient vector all ones.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 143, Theorem 4.2

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Separation_IsFacet
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical

namespace ChvatalPolytopes.Separation

/-- **Theorem 4.2** (Chvátal 1975, p. 143). Let `G = (V, E)` be a graph and let `E*` be the set of
its critical edges. If `G* = (V, E*)` is connected, then the inequality
`Σ (x_u : u ∈ V) ≤ α(G)` is a facet of `P(G)`.

`G*` is `criticalGraph G`; Mathlib's `Connected` includes `Nonempty V` (for `V = ∅` the
conclusion would be false, since the empty system defines `P(G)`). `α(G) = G.indepNum`, cast
to `ℝ`; the facet notion is the paper's (`IsFacet`: every defining linear system of `P(G)`
contains a positive multiple of the inequality). -/
theorem sum_le_indepNum_isFacet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : (criticalGraph G).Connected) :
    IsFacet (Shared.stablePolytope G) (fun _ => 1) (G.indepNum : ℝ) := by sorry

end ChvatalPolytopes.Separation
