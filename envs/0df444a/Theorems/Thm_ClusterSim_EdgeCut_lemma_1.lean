-- Prove2me | Theorems.Thm_ClusterSim_EdgeCut_lemma_1
-- name    : ClusterSim.EdgeCut.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:45.998867+00:00
-- url     : https://prove2.me/theorems/dbff6601-9f24-4f01-9686-01673be0f673
-- title:
--   Lemma 1 — cutting one edge: T(G, A) = Σ_{i=1}^8 c_i T(G′, A_i) with c_i = ±½, ρ_i states and O_i Pauli observables (pinned down)
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network and $e=uv$ any edge of $G$. For $i=1,\dots,8$ let $(G',\mathcal A_i)$ be the network obtained by cutting $e$ with the $i$-th triple $(O_i,\rho_i,c_i)$ of eqs. (12)–(19): the edge $u\to v$ is replaced by $u\to\triangleright(O_i)$ and $\triangleleft(\rho_i)\to v$. Then
--   $$T(G,\mathcal A)=\sum_{i=1}^8 c_i\,T(G',\mathcal A_i),\tag{11}$$
--   and for every $i$:
--   1. $c_i\in\{-\tfrac12,\tfrac12\}$;
--   2. $\rho_i$ is a state that is a pure projector: positive semidefinite, of trace $1$, with $\rho_i^2=\rho_i$;
--   3. $O_i$ is a Pauli observable: Hermitian with $O_i^2=I$;
--   4. $\rho_i$ is an eigenprojector of $O_i$ with eigenvalue $2c_i$: $O_i\rho_i=2c_i\,\rho_i$.
--
--   Items 1–4 are what makes every term a valid circuit: the $i$-th network measures the qubit produced at $u$ with $O_i$ and prepares the qubit required at $v$ in the state $\rho_i$. Lemma 1 is the basic step of the cluster simulation; applied to every edge between clusters it reduces the simulation of a circuit to the simulation of its clusters.
--
--   **Formalization Note** The paper states the lemma existentially ("there is a set of eight coefficients …, observables …, and states …"); the formalization states it for the paper's own data (12)–(19), which is stronger and is what the proof of Theorem 1 uses. "Valid quantum circuit" is pinned down as items 1–4. The lemma is stated for every tensor network, not only for networks of circuits, and the tensors need not be local; it holds in that generality.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 8, Lemma 1 (Supplemental Material §III; stated in the Letter on p. 3), eq. (11), with the data (12)–(19)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Cut

namespace ClusterSim.EdgeCut

open Matrix
open scoped ComplexOrder

/-- Lemma 1, p. 8 (stated in the Letter on p. 3), with the paper's own data (12)–(19): cutting a
single edge `e = uv` of a tensor network into `u → ▷(O_i)` and `◁(ρ_i) → v` gives eight networks
`(G′, A_i)` with `T(G, A) = Σ_{i=1}^8 c_i T(G′, A_i)` (eq. (11)); each coefficient is `±½`, each
`ρ_i` is a state (positive semidefinite, trace one, a projector), each `O_i` is a Pauli
observable (Hermitian, squaring to the identity), and `ρ_i` is an eigenprojector of `O_i` with
eigenvalue `2c_i`. -/
theorem lemma_1 (G : TensorNetwork) (e : G.E) :
    value G = ∑ i : Fin 8, (coef i : ℂ) * value (cut G {e} (fun _ => i)) ∧
      ∀ i : Fin 8,
        (coef i = 1 / 2 ∨ coef i = -1 / 2) ∧
        (eigProj i).PosSemidef ∧ (eigProj i).trace = 1 ∧ eigProj i * eigProj i = eigProj i ∧
        (pauli i).IsHermitian ∧ pauli i * pauli i = 1 ∧
        pauli i * eigProj i = (2 * coef i : ℂ) • eigProj i := by sorry

end ClusterSim.EdgeCut
