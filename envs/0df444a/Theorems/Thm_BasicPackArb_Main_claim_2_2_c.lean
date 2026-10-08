-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_2_c
-- name    : BasicPackArb.Main.claim_2_2_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:54.96309+00:00
-- url     : https://prove2.me/theorems/b0d3b7d3-68c3-44d9-90b6-5edb284e127d
-- title:
--   Claim 2.2 (c) — $v$ dominates the vertices of $X$ that reach it in $D[X]$ through good arcs
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots and $M$ a matroid on $S$, and suppose $(D,S,\pi)$ is $M$-connected. Let $X$ be a tight set and $v$ a vertex of $X$. Let $Y$ be the set of vertices $y\in X$ from which $v$ is reachable in $D[X]$ using only good arcs (an arc $uw$ is good if $S_u\subseteq\mathrm{Span}_M(S_w)$). Then $v$ dominates $Y$:
--   $$S_Y\subseteq\mathrm{Span}_M(S_v).$$
--
--   Domination propagates backwards along good arcs; with (b) this is how Claim 2.3 and the minimality argument of Claim 2.4 conclude.
--
--   **Formalization Note** $Y$ is `D.reachSetVia (IsGoodArc D π M) X v`. The claim's preamble hypotheses ($M$-connected, $X$ tight, $v\in X$) are kept as binders, as on the page, although part (c) does not need the first two. "$v$ dominates $Y$" is `Dominates π M {v} Y`.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4, Claim 2.2 (c)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- Claim 2.2 (c) (p. 4). Suppose `(D, S, π)` is `M`-connected, `X` is a tight set and `v ∈ X`.
If `Y` is the set of vertices of `X` from which `v` is reachable in `D[X]` using only good
arcs, then `v` dominates `Y`. -/
theorem claim_2_2_c {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hconn : MConnected D π M) (X : Finset V) (hX : IsTight D π M X) (v : V) (hvX : v ∈ X) :
    Dominates π M {v} (D.reachSetVia (IsGoodArc D π M) X v) := by sorry

end BasicPackArb.Main
