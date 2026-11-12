-- Prove2me | Theorems.Thm_BunkbedAux_involution_crosses
-- name    : BunkbedAux.involution_crosses
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:49:33.895158+00:00
-- url     : https://prove2.me/theorems/b86e35bb-f812-46d7-8635-00f9f8b4204e
-- title:
--   Path surgery: the involution turns a same-level connection into a cross-level one
-- statement:
--   This is the combinatorial heart of the involution argument by which Gladkov--Pak--Zimin prove their robustness lemma.
--
--   Work with the Wierman--Ziff model on Hollom's hypergraph, in the refined pair state space, and let $\Psi$ be a refined configuration. Fix a hyperedge $e$ whose refined state lies in $\Lambda^2_+$, and let $\phi = \texttt{phiExt}\,e$ be the involution that leaves the hyperedges before $e$ along the path $\rho$ untouched, applies the half-reflection $\eta$ at $e$, and applies the level swap $\rho$ to every hyperedge after $e$. Then
--
--   $$u_1 \leftrightarrow u_{10} \ \text{ in } \Psi \qquad \Longrightarrow \qquad u_1 \leftrightarrow u_{10}' \ \text{ in } \phi(\Psi).$$
--
--   That is, $\phi$ turns a same-level connection between the two endpoints into a cross-level one. Since $\phi$ is a weight-preserving involution, the configurations in which some hyperedge lies in $\Lambda^2_+$ therefore contribute *equally* to the two connection events, and cancel from their difference — which reduces the robustness lemma to the configurations avoiding $\Lambda^2_+$, where the model degenerates to the alternative bunkbed hypergraph model and Hollom's computation applies.
--
--   **How the connection is transported.** The proof exhibits a map on vertices, reflecting the level of every non-transversal vertex lying strictly beyond $e$ along $\rho$ and fixing everything else. The source $u_1$ sits at the start of $\rho$ and is fixed; the target $u_{10}$ sits at the end and is always reflected, which is exactly why a same-level connection becomes a cross-level one. The work is in checking that the image of a path is still a path, which is a case analysis over the four kinds of edge: a post, an edge of a hyperedge before $e$, an edge of a hyperedge after $e$, and an edge of $e$ itself. The last case is where Proposition 3.7 is used.
--
--   **Formalization note.** The vertex map is *not* a graph homomorphism, and the argument as printed in the source is slightly loose on this point. Transversal vertices cannot be reflected — each serves one hyperedge before $e$ and one after — so an edge joining a transversal vertex to a non-transversal one has exactly one endpoint moved, and its image is not an edge. What is true, and what is proved here, is that adjacency is carried to *reachability*: the mismatch is repaired using the post over the transversal vertex, which is present in every configuration. Reachability then transports along a walk by induction.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Lemma 3.8 (p. 5-6) with its proof.

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **Lemma 3.8 of Gladkov-Pak-Zimin** (path surgery). If the state of hyperedge `e` lies in
`Λ²₊`, then the involution `phiExt e` carries a same-level connection `u₁ ↔ u₁₀` to a
cross-level connection `u₁ ↔ u₁₀'`. -/
theorem involution_crosses (e : Fin 6) (Ψ : Fin 6 → WZExt)
    (he : WZExt.inLamSq (Ψ e) = true)
    (hr : (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
      ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable
      ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) := by
  sorry

end BunkbedAux
