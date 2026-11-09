-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_eulerian_expanding_subgraph
-- name    : BinaryThreeLCC.Main.eulerian_expanding_subgraph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:45.789712+00:00
-- url     : https://prove2.me/theorems/dfbced4a-12d5-488f-b67b-5a6b102cf02a
-- title:
--   Lemma 4.2 — Eulerian expanding subgraph
-- statement:
--   Let $D=(V,F)$ be a finite directed graph without parallel directed edges, with $V$ nonempty. Let $n\ge1$ be an integer and $\delta\ge0$. Assume $|V|\le n$ and every vertex has outdegree at least $\delta n$. Then $D$ has a possibly non-induced subgraph $D'=(V',F')$ satisfying
--
--   $$|V'|\ge\frac{\delta^2n}{8},\qquad
--   d_{\rm in}^{D'}(v)=d_{\rm out}^{D'}(v)\quad(v\in V'),$$
--
--   and, for every $S\subseteq V'$,
--
--   $$e_{D'}(S,V'\setminus S)\ge\frac{\delta^4}{96}|S|\,|V'\setminus S|.$$
--
--   Eulerian means balance at every vertex and imposes no connectedness requirement. The retained edge identities and their endpoints certify that this is a subgraph of the original graph.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: the minimum outdegree over V → V nonempty, n positive, and a pointwise outdegree lower bound; reason: the displayed minimum is defined only for a nonempty vertex set; this prevents a vacuous empty input
--   - generalization: positive density δ used in the surrounding proof → δ ≥ 0, without an upper bound; reason: the same conclusion holds at δ=0 by taking an edgeless subgraph; every positive source instance is retained
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 4.2, printed p. 11, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Graphs

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Lemma 4.2. The minimum outdegree has its nonempty domain. -/
theorem eulerian_expanding_subgraph {V E : Type} [Fintype V] [Fintype E] [Nonempty V]
    (G : ContPatrol.Multigraph V E) (hparallel : NoParallel G)
    (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hsize : Fintype.card V ≤ n)
    (hdegree : ∀ v, δ * n ≤ (outDegree G v : ℝ)) :
    ∃ D : DirectedSubgraph G,
      δ ^ 2 * n / 8 ≤ (D.vertices.card : ℝ) ∧
      Eulerian D.graph ∧ CutDense D.graph (δ ^ 4 / 96) := by sorry

end BinaryThreeLCC.Main
