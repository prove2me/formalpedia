-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_10_6
-- name    : ApproxCactus.Main.lemma_10_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:03:02.917783+00:00
-- url     : https://prove2.me/theorems/7464d89c-7f2c-47ac-82ff-a4878561bf22
-- title:
--   Lemma 10.6 — in a graphic-k-daisy with the clover-property, the bags containing a clique K ⊄ X form a nonempty subpath
-- statement:
--   Let $G$ be a finite graph and $F=(O,\mathcal V)$ a graphic-$k$-daisy of $G$ with the clover-property and centre $X=\bigcap_{o}V_o$. Let $K$ be a clique of $G$ with $K\not\subseteq X$. Then the set of nodes $x$ with $K\subseteq V_x$ induces a nonempty subpath of $O$ (it is nonempty, not all of $V(O)$, and induces a connected subgraph of $O$). In particular some bag $V_x$ contains $K$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: graph-decomposition (H, V) with H a strong cactus, a cycle Z_ℓ or a star, and designated P-nodes → Decomp G: a finite loopless multigraph (node type, edge type, endpoint map), bags as Finsets, a set of P-nodes, (H1) and (H2); reason: cacti, cycles and stars are loopless; parallel edges are kept so that Z_2 is a 2-cycle; any finite multigraph can be relabelled by types in Type
--   - reading: clique of G → any Finset K with G.IsClique K, including ∅ and singletons; reason: the source does not exclude them; including them is the stronger reading of the conclusion
--   - encoding: "induces a nonempty subpath of O" → the node set is nonempty, is not all of V(O), and induces a connected subgraph of the cycle O; reason: in a cycle Z_ℓ a node set induces a path exactly when it is a nonempty proper subset inducing a connected subgraph
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 10.6, printed p. 106 (PDF p. 109)

import Definitions.Def_ApproxCactus_Main_Flowers

namespace ApproxCactus.Main

/-- **Lemma 10.6**, p. 106: let `F = (O, V)` be a graphic-`k`-daisy of `G` with the
clover-property and centre `X`, and `K` a clique of `G` with `K ⊄ X`. Then the set of nodes `x`
with `K ⊆ V_x` induces a nonempty subpath of `O` (nonempty, not all of `V(O)`, inducing a connected
subgraph of the cycle `O`); in particular some bag contains `K`. -/
theorem lemma_10_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (F : Decomp G) (hF : IsGraphicDaisy G k F) (hcl : HasClover k F)
    (K : Finset V) (hK : G.IsClique (K : Set V)) (hKX : ¬ K ⊆ F.centre) :
    {x : F.N | K ⊆ F.bag x}.Nonempty ∧ {x : F.N | K ⊆ F.bag x} ≠ Set.univ ∧
      (F.skeleton.induce {x : F.N | K ⊆ F.bag x}).Connected ∧
      ∃ x : F.N, K ⊆ F.bag x := by sorry

end ApproxCactus.Main
