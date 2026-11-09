-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_cheeger_regular_multigraph
-- name    : BinaryThreeLCC.Main.cheeger_regular_multigraph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:56.834131+00:00
-- url     : https://prove2.me/theorems/2374dc64-0284-4ae4-9016-ec6429968b25
-- title:
--   Fact 3.6 — Cheeger inequality for regular multigraphs
-- statement:
--   Let $G=(V,E)$ be a finite undirected $d$-regular multigraph, with $d>0$ and $|V|\ge2$, allowing loops and parallel edge copies. Its adjacency counts loops twice, consistently with degree. For each $S\subseteq V$ with $1\le|S|\le|V|/2$, let
--
--   $$\phi(S)=\frac{e(S,V\setminus S)}{d|S|},\qquad
--   \phi(G)=\min_{1\le|S|\le|V|/2}\phi(S).$$
--
--   If $\lambda_2$ is the second smallest eigenvalue, with multiplicity, of $I-A_G/d$, then
--
--   $$\lambda_2\ge\frac{\phi(G)^2}{2}.$$
--
--   Disconnected graphs remain in scope. The Proved chain Cheeger theorem is available for a connected graph after normalization; the graph-to-chain identifications are not extra assumptions of this result.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - reading: Section 3 allows loops but Definition 3.1 writes two-element edges → labelled endpoint pairs, loops of length one, parallel-edge cycles of length two, and loops counted twice in undirected degrees and adjacency; reason: the standing multigraph convention and A_T = Q_T + Q_T transpose control the interpretation
--   - encoding: a literal second eigenvalue and a minimum of ratios → |V| ≥ 2 and d > 0; a finite nonempty conductance set and the published Hermitian eigenvalues sorted with multiplicity; reason: these are precisely the domains of the displayed formulas, including disconnected instances
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 3.6, printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Spectral

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Fact 3.6, including disconnected graphs, loops and parallel edge copies.
For the connected case normalize to the uniform reversible Markov chain and use
MarkovMixing.cheeger_inequality. The bridge requires no connectedness here. -/
theorem cheeger_regular_multigraph {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (G : ContPatrol.Multigraph V E) (d : ℕ)
    (hd : 0 < d) (hregular : ∀ v, G.deg v = d) :
    conductance G d ^ 2 / 2 ≤ secondSmallest (normalizedLaplacian G d) := by sorry

end BinaryThreeLCC.Main
