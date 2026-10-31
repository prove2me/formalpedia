-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_eqs_31_32
-- name    : ClusterSim.EdgeCut.eqs_31_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:46.82629+00:00
-- url     : https://prove2.me/theorems/5c25dddc-6bdd-4de7-b950-a9647e0794e2
-- title:
--   Eqs. (31)–(32) — cutting a set C of edges: T(G, A) = Σ_{s∈[8]^C} c_s T(G′, A_s), c_s = Π_{e∈C} c_{s_e}
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network and $C$ any finite set of its edges. For $s=(s_e)_{e\in C}\in[8]^C$ let $(G',\mathcal A_s)$ be the network obtained by cutting every edge $e\in C$ with the triple $(O_{s_e},\rho_{s_e},c_{s_e})$, and $c_s=\prod_{e\in C}c_{s_e}$. Then
--   $$T(G,\mathcal A)=\sum_{s\in[8]^C}c_s\,T(G',\mathcal A_s).$$
--
--   In the proof of Theorem 1 this is applied with $C=E_{\mathrm{cut}}$, the edges between clusters; it expresses the value of the circuit through $8^{|C|}$ networks in which no qubit passes between clusters.
--
--   **Formalization Note** The identity is stated for an arbitrary set $C$ (no clustering is needed) and for arbitrary, not necessarily local, tensors.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 9, proof of Theorem 1, eqs. (31)–(32)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Cut

namespace ClusterSim.EdgeCut

/-- Eqs. (31)–(32), proof of Theorem 1, p. 9: cutting every edge of a finite set `C` of edges at
once, `T(G, A) = Σ_{s ∈ [8]^C} c_s T(G′, A_s)` with `c_s = Π_{e ∈ C} c_{s_e}`. -/
theorem eqs_31_32 (G : TensorNetwork) (C : Finset G.E) :
    value G = ∑ s : C → Fin 8, (coefS s : ℂ) * value (cut G C s) := by sorry

end ClusterSim.EdgeCut
