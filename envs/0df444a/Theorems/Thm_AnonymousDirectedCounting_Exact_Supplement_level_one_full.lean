-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_level_one_full
-- name    : AnonymousDirectedCounting.Exact.Supplement.level_one_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:31.146751+00:00
-- url     : https://prove2.me/theorems/0d00886e-4a73-426a-b8dc-cd5f71a248c2
-- title:
--   Lemma 16 — level one is full in every realization
-- statement:
--   With the Appendix F data ($q\ge2$, distinct triples), let $\mathcal V$ be the reference leader vista after round $B$. Fix any realization of $\mathcal V$ with one leader, on any agent set $V$, with any observer $x$ whose round-$B$ vista is $\mathcal V$. For $1\le r\le B-1$ let $S_r\subseteq V$ be the union of the fibers of the nodes visible at level $r$ of $\mathcal V$. Then
--   $$S_1=V.$$
--
--   No assumption is made on the shape of the realization or on its fiber sizes; the lemma is the step that forces every one-leader realization to account for all of the leader's outgoing arcs.
--
--   Differences from the source:
--   - encoding: a realization is a finite network prefix through round t, strongly connected in each round → a network strongly connected in every round (published Admissible); reason: a prefix extends by repeating a strongly connected round, and rounds after t do not affect round-t vistas
--   - encoding: the union of the fibers of the nodes visible at level 1, and the agent set V → unionFibers G 1 (agentLevel G B x 1) and Finset.univ; reason: published definitions
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 30 (PDF p. 32), Lemma 16

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_X3CReduction

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 16, printed p. 30 (PDF p. 32). In every one-leader realization of the reference leader
vista `𝒱` — any network with one leader, strongly connected in every round, and any agent `x` whose
round-`B` history is `𝒱` — the union `S_1` of the fibers of the visible level-1 nodes is the whole
agent set. -/
theorem level_one_full (q m : ℕ) (S : Fin m → Finset ℕ) (hS : IsX3CInstance q m S)
    {N : ℕ} (G : NetworkModel N) (hG : Admissible G) (hlead : G.leaders.card = 1)
    (x : Fin N) (hx : history G (baseB q) x = refVista q m S) :
    unionFibers G 1 (agentLevel G (baseB q) x 1) = Finset.univ := by sorry

end AnonymousDirectedCounting.Exact.Supplement
