-- Prove2me | Theorems.Thm_EndpointPairMultiplicitySimpleGraph
-- name    : EndpointPairMultiplicitySimpleGraph
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:40:52.681269+00:00
-- url     : https://prove2.me/theorems/136d296c-9313-45f8-93e3-aedf0b5dfad7
-- title:
--   Endpoint Pair Multiplicity Simple Graph
-- statement:
--   Let $A$ be a finite set of indices and let
--   $\epsilon:A\to \operatorname{Sym}^{2}(V)$ assign to each index an unordered
--   pair of vertices of $V$.  Suppose that no assigned pair is diagonal, and that
--   for every unordered pair $e$ in the image of $\epsilon$, at most two indices
--   of $A$ are assigned to $e$.  Then there is a simple graph $G$ on $V$
--   with finite edge set such that the edge set of $G$ is exactly the image of
--   $\epsilon$, and
--   $$
--     |A|/2\le |E(G)|.
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `EndpointPairMultiplicitySimpleGraph`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/EndpointPairMultiplicitySimpleGraph.lean#L1-L64

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
open scoped Real
noncomputable section

lemma EndpointPairMultiplicitySimpleGraph {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (A : Finset ι) (endpoint : ι → Sym2 V)
    (h_nondiag : ∀ i ∈ A, ¬ (endpoint i).IsDiag)
    (h_multiplicity : ∀ e ∈ A.image endpoint,
      (A.filter (fun i => endpoint i = e)).card ≤ 2) :
    ∃ G : SimpleGraph V, ∃ (_ : Fintype G.edgeSet),
      (A.card : ℝ) / 2 ≤ (G.edgeFinset.card : ℝ) ∧
        G.edgeFinset = A.image endpoint := by sorry
