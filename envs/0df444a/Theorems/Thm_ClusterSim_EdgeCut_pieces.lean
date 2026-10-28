-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_pieces
-- name    : ClusterSim.EdgeCut.pieces
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:29.284437+00:00
-- url     : https://prove2.me/theorems/6c58ddce-e57f-4dbb-b7d1-caaf15f536dc
-- title:
--   Proof of Theorem 1, p. 10 — for a (K, d)-clustered network every cut network (G′, A_s) splits into r pieces of at most d qubits
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network with a $(K,d)$-clustering into $r$ clusters, and let $s\in[8]^{E_{\mathrm{cut}}}$. In the induced clustering of the cut network $(G',\mathcal A_s)$ (original vertices keep their clusters, the observable vertex $\triangleright_e$ joins the cluster of the source of $e$ and the state vertex $\triangleleft_e$ that of its target):
--   1. no edge connects two different clusters, and
--   2. every cluster needs at most $d$ qubits: $d(S'_i)\le d$ for $i=1,\dots,r$.
--
--   So $(G',\mathcal A_s)$ consists of $r$ pieces, not counting the final observable $O_f$, each of which can be executed on a $d$-qubit device; this is why one sample of the simulation costs $r$ runs of a $d$-qubit device.
--
--   **Formalization Note** "Pieces" are the clusters of the induced clustering; "consists of $r$ pieces" is formalized as the absence of cut edges, and "can be executed on a $d$-qubit quantum computer" as the qubit count $d(S'_i)$ ($\triangleleft$ vertices plus edges entering from other clusters) being at most $d$.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 10, proof of Theorem 1 (unnumbered sentence after eq. (33))

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Clustering

namespace ClusterSim.EdgeCut

/-- Proof of Theorem 1, p. 10: if `G` is `(K, d)`-clustered, then for every `s ∈ [8]^{E_cut}` the cut
network `(G′, A_s)` consists of `r` pieces, each runnable on a `d`-qubit device: in the induced
clustering of `(G′, A_s)` no edge connects different clusters, and every cluster needs at most `d`
qubits. -/
theorem pieces {G : TensorNetwork} {r K d : ℕ} (P : Clustering G r) (hP : P.IsClustered K d)
    (s : P.Ecut → Fin 8) :
    (P.cutClustering s).Ecut = ∅ ∧ ∀ i, (P.cutClustering s).qubits i ≤ d := by sorry

end ClusterSim.EdgeCut
