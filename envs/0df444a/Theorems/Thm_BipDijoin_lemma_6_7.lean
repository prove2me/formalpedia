-- Prove2me | Theorems.Thm_BipDijoin_lemma_6_7
-- name    : BipDijoin.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:21.405439+00:00
-- url     : https://prove2.me/theorems/978f864e-e66b-4823-be9a-7ef7ccea3d9f
-- title:
--   Lemma 6.7 — deleting a perfectly matchable set loses at most $(1-\eta)|U|/2$ of $\Phi_\eta$
-- statement:
--   Let $G=(L\cup R,E)$ be a bipartite multigraph and $U\subseteq V(G)$ such that $G[U]$ has a perfect matching, and let $H=G-U$. For every $\eta\in[0,1]$, every balanced server flow on $G$ and every balanced server flow on $H$,
--   $$\Phi_\eta(G)-\Phi_\eta(H)\le(1-\eta)\,\frac{|U|}{2}.$$
--
--   This is the extension of the [BHR19] potential argument to contractions: deleting a balanced set of size $2k$ destroys at most $(1-\eta)k$ units of potential.
--
--   Differences from the source:
--   - reading: Φ_η(G) and Φ_η(H), defined through unique load vectors [BHR19] → the potentials of arbitrary balanced server flows on G and on H; reason: the uniqueness is cited; the statement for all balanced flows gives the source's
--   - reading: G[U] is perfectly matched → G[U] has a perfect matching; reason: the proof uses only a perfect matching of G[U]
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Lemma 6.7, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsServerFlow

set_option autoImplicit false

namespace BipDijoin

/-- **Lemma 6.7** (Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6),
p.31 = PDF p.33). "Let U be any subset of graph G = (L ∪ R, E) such that G[U] is perfectly matched
and H := G − U be the graph obtained after deleting the subset U. For every η ∈ [0, 1],
Φ_η(G) − Φ_η(H) ≤ (1 − η)|U|/2."

Let `G` be a well-formed bipartite multigraph and `U ⊆ V(G)` such that `G[U]` has a perfect
matching; let `H = G − U`. For every `η ∈ [0, 1]`, every balanced server flow `x` on `G` and every
balanced server flow `y` on `H`: `Φ_η(x) − Φ_η(y) ≤ (1 − η)|U|/2`.

**Formalization Note.** "G[U] is perfectly matched" is read as "G[U] has a perfect matching". The
potentials are those of arbitrary balanced flows of `G` and of `H` (their loads are unique by
[BHR19], which is not needed here). -/
theorem lemma_6_7 (G : BipGraph) (hG : G.WF) (U : Finset ℕ) (hUV : U ⊆ G.V)
    (hpm : (G.induced U).HasPerfectMatching) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (x y : ℕ → ℝ) (hx : G.IsBalancedServerFlow x) (hy : (G.deleteVerts U).IsBalancedServerFlow y) :
    G.Phi η x - (G.deleteVerts U).Phi η y ≤ (1 - η) * (U.card : ℝ) / 2 := by sorry

end BipDijoin
