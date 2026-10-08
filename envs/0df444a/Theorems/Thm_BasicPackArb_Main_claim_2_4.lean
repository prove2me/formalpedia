-- Prove2me | Theorems.Thm_BasicPackArb_Main_claim_2_4
-- name    : BasicPackArb.Main.claim_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:44.40128+00:00
-- url     : https://prove2.me/theorems/f7c27c8d-345f-414b-a55b-cebb7c903b2e
-- title:
--   Claim 2.4 — some bad arc uv and s ∈ S_u \ Span(S_v) keep (D−uv, S′, π′) M′-connected
-- statement:
--   Let $(D,S,\pi)$ be a digraph with roots, $D=(V,A)$, and $M$ a matroid on $S$, with $\pi$ $M$-independent and $(D,S,\pi)$ $M$-connected, and suppose $D$ has at least one bad arc. Then there exist a bad arc $uv\in A$ and an element $s\in S_u\setminus\mathrm{Span}_M(S_v)$ such that $(D',S',\pi')$ is $M'$-connected, where $D'=D-uv$, $S'=S\cup\{s'\}$ with a new element $s'$, $M'$ is obtained from $M$ by making $s'$ parallel to $s$, and $\pi'$ extends $\pi$ by placing $s'$ at $v$:
--   $$\rho_{D'}(X)\ \ge\ r_{M'}(S')-r_{M'}(S'_X)\qquad\text{for all non-empty }X\subseteq V.$$
--
--   Together with the lifting step it completes the induction on $|A|$ in the proof of sufficiency of Theorem 1.6.
--
--   **Formalization Note** The claim is stated inside the proof of sufficiency after "we may assume that A is not empty and there exists at least one bad arc"; these standing hypotheses ($\pi$ $M$-independent, $M$-connected, a bad arc exists) are binders. $S'$ is `Option S` with $s'$ = `none`; $M'$ = `extMatroid M s`, $\pi'$ = `extPlacement D π a`, $D'$ = `D.deleteArc a`. $M'$-connectedness is written additively in $\mathbb{N}_\infty$.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 5, Claim 2.4 (in the proof of sufficiency in Theorem 1.6)

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_BasicPackArb_Main_ProofObjects

namespace BasicPackArb.Main

/-- Claim 2.4 (p. 5), under the standing hypotheses of the sufficiency proof (`π` is
`M`-independent, `(D, S, π)` is `M`-connected) and its case assumption that a bad arc exists.
There exist a bad arc `a = uv ∈ A` and `s ∈ S_u \ Span_M(S_v)` such that `(D', S', π')` is
`M'`-connected, where `D' = D − uv`, `S' = S ∪ {s'}`, `M'` makes `s'` parallel to `s`, and `π'`
places `s'` at `v`. -/
theorem claim_2_4 {V Arc S : Type*} [Fintype V] [DecidableEq V] [DecidableEq Arc] [Fintype S]
    (D : Digraph V Arc) (π : S → V) (M : Matroid S) (hM : M.E = Set.univ)
    (hind : MIndependent π M) (hconn : MConnected D π M)
    (hbad : ∃ a ∈ D.arcs, ¬ IsGoodArc D π M a) :
    ∃ a ∈ D.arcs, ¬ IsGoodArc D π M a ∧ ∃ s : S, π s = D.tail a ∧
      s ∉ Span M (π ⁻¹' {D.head a}) ∧
      MConnected (D.deleteArc a) (extPlacement D π a) (extMatroid M s) := by sorry

end BasicPackArb.Main
