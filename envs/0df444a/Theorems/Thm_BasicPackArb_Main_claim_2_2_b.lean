-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_2_b
-- name    : BasicPackArb.Main.claim_2_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:44.090046+00:00
-- url     : https://prove2.me/theorems/21ade4b1-4fac-4af5-8440-bd0463332fb2
-- title:
--   Claim 2.2 (b) — the vertices of a tight $X$ that reach $v$ in $D[X]$ form a tight set dominating $X$
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots and $M$ a matroid on $S$, and suppose $(D,S,\pi)$ is $M$-connected. Let $X$ be a tight set and $v$ a vertex of $X$. Let
--   $$Y=\{y\in X:\ v\text{ is reachable from }y\text{ in }D[X]\},$$
--   the set of vertices of $X$ from which there is a directed path to $v$ inside $D[X]$. Then $v\in Y\subseteq X$, $Y$ is tight, and $Y$ dominates $X$, i.e. $S_X\subseteq\mathrm{Span}_M(S_Y)$.
--
--   This lets the proof shrink a tight set to the part that reaches a given vertex without losing tightness or domination.
--
--   **Formalization Note** $Y$ is `D.reachSet X v`, the filter of $X$ by "there is a directed path from $y$ to $v$ using arcs of $A$ with both ends in $X$". The claim's preamble hypotheses ($M$-connected, $X$ tight, $v\in X$) are binders. Tightness is written additively in $\mathbb{N}_\infty$.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 4, Claim 2.2 (b)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- Claim 2.2 (b) (p. 4). Suppose `(D, S, π)` is `M`-connected, `X` is a tight set and `v ∈ X`.
If `Y` is the set of vertices of `X` from which `v` is reachable in `D[X]`, then `v ∈ Y ⊆ X`,
`Y` is tight and `Y` dominates `X`. -/
theorem claim_2_2_b {V Arc S : Type*} [Fintype V] [DecidableEq V] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hconn : MConnected D π M) (X : Finset V) (hX : IsTight D π M X) (v : V) (hvX : v ∈ X) :
    v ∈ D.reachSet X v ∧ D.reachSet X v ⊆ X ∧
      IsTight D π M (D.reachSet X v) ∧
      Dominates π M (D.reachSet X v) X := by sorry

end BasicPackArb.Main
