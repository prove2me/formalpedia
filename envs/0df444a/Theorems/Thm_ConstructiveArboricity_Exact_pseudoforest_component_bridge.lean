-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_pseudoforest_component_bridge
-- name    : ConstructiveArboricity.Exact.pseudoforest_component_bridge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:28.944752+00:00
-- url     : https://prove2.me/theorems/54e8fee3-0394-47f8-a37f-80948c4db86d
-- title:
--   Pseudoforest counting and component definitions agree
-- statement:
--   Let $G$ be a finite simple graph and $S$ a subset of its edge identities. The counting definition of a pseudoforest agrees with the component definition:
--
--   $$
--   \bigl(\forall X\subseteq V,\ |E_S(X)|\le |X|\bigr)
--   \quad\Longleftrightarrow\quad
--   \text{every component of }(V,S)\text{ can be made acyclic by deleting at most one edge}.
--   $$
--
--   The condition on the right is equivalent to every connected component containing at most one cycle. This bridge is required to use the published counting predicate in the source's component-based arguments; it is a statement to be proved, rather than an assumed compatibility condition.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph with its edge sets → vertices Fin n, edge identities Fin m, an injective unordered endpoint map, and color fibers; reason: every finite simple graph admits such labels; isolated vertices and empty color classes are retained
--   - encoding: at most one cycle in each connected component → each component becomes acyclic after deletion of at most one of its edges; reason: equivalent for finite simple graphs; the counting-to-component equivalence is the conclusion
--   - encoding: a pseudoforest has at most one cycle in each connected component → the published counting predicate requires every finite vertex set to span at most its cardinality in undirected edges; reason: equivalent for finite simple graphs; the separate pseudoforest_component_bridge target explicitly relates this predicate to the component definition
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, §2, p.7, definition of pseudoforest (representation bridge)

import Mathlib
import Definitions.Def_ConstructiveArboricity_Exact_Graph

namespace ConstructiveArboricity.Exact

/-- Bridge from the published counting predicate to the component definition
in Gholami et al., STOC 2027 submission #1476 (October 2026), §2, p.7.
PDF sha256 9aa896d448cf63b4f502235eca19f59eb0468fad89783d21467b281518e3c512.
This equivalence is a target, never an input to a source theorem. -/
theorem pseudoforest_component_bridge (G : Graph) (S : Set (Fin G.m)) :
    G.IsPseudoforest S ↔ G.ComponentPseudoforest S := by sorry

end ConstructiveArboricity.Exact
