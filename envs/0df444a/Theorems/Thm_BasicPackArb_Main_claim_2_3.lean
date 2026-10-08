-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_3
-- name    : BasicPackArb.Main.claim_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:58.60772+00:00
-- url     : https://prove2.me/theorems/da1d7368-7114-42e7-b92e-3fa85a942d99
-- title:
--   Claim 2.3 — with no bad arc, $|S_v|$ copies of each vertex $v$ form an M-basic packing
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots, $D=(V,A)$, and $M$ a matroid on $S$, such that $\pi$ is $M$-independent and $(D,S,\pi)$ is $M$-connected. If $D$ has no bad arc (every arc $uv\in A$ satisfies $S_u\subseteq\mathrm{Span}_M(S_v)$), then taking $|S_v|$ times each vertex $v$ gives an $M$-basic packing of arborescences in $(D,S,\pi)$: for every $s\in S$, let $T_s$ be the arborescence consisting of the single vertex $\pi(s)$ and no arc. Then $(T_s)_{s\in S}$ is an $M$-basic packing; equivalently, $S_v$ is a base of $M$ for every vertex $v$.
--
--   This is the base case of the induction on $|A|$ that proves sufficiency in Theorem 1.6.
--
--   **Formalization Note** The claim sits inside the proof of sufficiency, whose standing hypotheses ($\pi$ $M$-independent, $(D,S,\pi)$ $M$-connected) are stated explicitly. The conclusion is the packing itself: `IsBasicPacking D π M (fun s => Arborescence.single D (π s))`.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 5, Claim 2.3 (in the proof of sufficiency in Theorem 1.6)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- Claim 2.3 (p. 5), with the standing hypotheses of the sufficiency proof (`π` is
`M`-independent and `(D, S, π)` is `M`-connected). If there is no bad arc, then taking `|S_v|`
times each vertex `v` (the single-vertex arborescence at `π s` for every `s ∈ S`) gives an
`M`-basic packing of arborescences in `(D, S, π)`. -/
theorem claim_2_3 {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hind : MIndependent π M) (hconn : MConnected D π M)
    (hgood : ∀ a ∈ D.arcs, IsGoodArc D π M a) :
    IsBasicPacking D π M (fun s => Arborescence.single D (π s)) := by sorry

end BasicPackArb.Main
