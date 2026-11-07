-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_9_packing
-- name    : ContractionLemma.lemma_A_9_packing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:45.113915+00:00
-- url     : https://prove2.me/theorems/4fde6036-50c7-459f-bd49-d2f2aea9f04f
-- title:
--   Lemma A.9 — packing: labels and at most $3M/L$ packets with orientation and small groups
-- statement:
--   Let $G$ be a bipartite network with $M$ edges, let $\Delta$ be at least its maximum degree, let $L=2^a$ and $Q=64^{2a}$, and suppose
--
--   $$
--   M\ge 2Q^2\Delta,\qquad M\ge LQ.
--   $$
--
--   Then there are labels $\phi(u),\psi(v)\in\{1,\dots,64\}^a$ and a placement of the edges into at most $3M/L$ packets of $L$ slots such that orientation holds, with its "in particular" clause, and every coordinate and symbol have at most $3M/64$ edges on each side. Moreover one deterministic machine computes such labels and such a placement from the encoded graph, $a$ and $\Delta$ in at most $C(N+1)^C$ steps.
--
--   The packing makes every shift of level $i$ block diagonal for the level-$i$ grouping, into 64 small groups.
--
--   **Formalization Note** The first part holds for any finite types of vertices and edges, and the second for graphs on `Fin` types. The lemma states no space bound, so the machine clause has none.
--
--   Differences from the source:
--   - reading: in deterministic polynomial time one can choose → one machine with output tape within C(N+1)^C steps, N the length of the unary encoding of the graph, a, ∆; reason: the paper names no input encoding and all quantities are polynomially related to the encoded graph
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.9, pp.60–61; proof pp.84–86

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **Lemma A.9 (Packing)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), pp.60–61 (PDF pp.63–64); proof pp.84–86.

Let `G` be a bipartite network (here: its graph) with `M` edges, let `∆` be at least its
maximum degree, let `Q = 64^{2a}` and suppose `M ≥ 2Q²∆` and `M ≥ LQ` (`L = 2^a`).
1. There are labels `ϕ(u), ψ(v) ∈ {1, …, 64}^a` and a placement of the edges into at most
   `3M/L` packets of `L` slots such that (a) orientation holds, together with its "in
   particular" clause, and (b) the groups are small.
2. (computation) Such labels and placement are output by a deterministic machine in
   polynomial time: `C (N+1)^C` steps on the encoded graph, `a` and `∆`.

**Formalization Note.** Part 1 is stated for any finite types of row vertices, column
vertices and edges; part 2 for graphs on `Fin` types (`BipGraph`). The lemma states no space
bound, so none is claimed. -/
theorem lemma_A_9_packing :
    (∀ {U W E : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] [Fintype E]
        (rowOf : E → U) (colOf : E → W) (a Δ : ℕ),
        (∀ u, (Finset.univ.filter fun e => rowOf e = u).card ≤ Δ) →
        (∀ w, (Finset.univ.filter fun e => colOf e = w).card ≤ Δ) →
        2 * (64 ^ (2 * a)) ^ 2 * Δ ≤ Fintype.card E →
        2 ^ a * 64 ^ (2 * a) ≤ Fintype.card E →
        ∃ pk : Packing U W E a, pk.Orientation rowOf colOf ∧ pk.SameSymbolOnShift rowOf colOf ∧
          pk.SmallGroups rowOf colOf ∧ pk.FewPackets) ∧
    (∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (C : ℕ),
      ∀ (G : BipGraph) (a Δ : ℕ),
        (∀ u, (Finset.univ.filter fun e => G.rowOf e = u).card ≤ Δ) →
        (∀ w, (Finset.univ.filter fun e => G.colOf e = w).card ≤ Δ) →
        2 * (64 ^ (2 * a)) ^ 2 * Δ ≤ G.M →
        2 ^ a * 64 ^ (2 * a) ≤ G.M →
        ∃ pk : Packing (Fin G.nr) (Fin G.nc) (Fin G.M) a,
          pk.Orientation G.rowOf G.colOf ∧ pk.SameSymbolOnShift G.rowOf G.colOf ∧
          pk.SmallGroups G.rowOf G.colOf ∧ pk.FewPackets ∧
          ∃ σ : ℝ, RunsWithin A outA (G.inputWord a Δ) (G.packingWord pk)
            (C * (((G.inputWord a Δ).length : ℝ) + 1) ^ C) σ) := by sorry

end ContractionLemma
