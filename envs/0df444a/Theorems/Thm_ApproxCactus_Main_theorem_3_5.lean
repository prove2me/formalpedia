-- Prove2me | Theorems.Thm_ApproxCactus_Main_theorem_3_5
-- name    : ApproxCactus.Main.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:56.296241+00:00
-- url     : https://prove2.me/theorems/4eaa4ff6-15ae-4472-88f4-b7b1f4d311bc
-- title:
--   Theorem 3.5 (Flower-Dichotomy Theorem) — every k-flower is a strong k-anemone or a k-daisy
-- statement:
--   For every $k\in\mathbb N$, every $k$-flower $O$ of a finite graph $G$ is a strong $k$-anemone or a $k$-daisy.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: graph-decomposition (H, V) with H a strong cactus, a cycle Z_ℓ or a star, and designated P-nodes → Decomp G: a finite loopless multigraph (node type, edge type, endpoint map), bags as Finsets, a set of P-nodes, (H1) and (H2); reason: cacti, cycles and stars are loopless; parallel edges are kept so that Z_2 is a 2-cycle; any finite multigraph can be relabelled by types in Type
--   - encoding: a path contained in O → a node set J inducing a connected subgraph of the cycle O; reason: in a cycle the vertex sets of paths are exactly the nonempty node sets inducing a connected subgraph
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Theorem 3.5, printed p. 25 (PDF p. 28)

import Definitions.Def_ApproxCactus_Main_Flowers

namespace ApproxCactus.Main

/-- **Theorem 3.5 (Flower-Dichotomy Theorem)**, p. 25: for every `k`, every `k`-flower is a strong
`k`-anemone or a `k`-daisy. -/
theorem theorem_3_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (O : Decomp G) (hO : IsFlower k O) :
    IsStrongAnemone k O ∨ IsDaisy G k O := by sorry

end ApproxCactus.Main
