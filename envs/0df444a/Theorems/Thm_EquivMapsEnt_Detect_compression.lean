-- Prove2me | Theorems.Thm_EquivMapsEnt_Detect_compression
-- name    : EquivMapsEnt.Detect.compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:35.908982+00:00
-- url     : https://prove2.me/theorems/5702834f-1eb0-4ee1-976b-f92aadf640f7
-- title:
--   Proof of Theorem 5.1, pp. 14–15: the compression of the lift to an invariant finite dimensional subspace
-- statement:
--   Let $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$ be a complex linear map, let $\mu$ be a finite left invariant measure on the unitary group $U_n$, and let $H=L^2(U_n,\mathbb C^N;\mu)$ carry the regular action $V(W)\psi(U)=\psi(W^{-1}U)$ of equation (22). Let $\Phi$ be the lift of equation (23), $\Phi(X)\psi=(\phi(U^*XU)\psi_U)_{U\in U_n}$, given through its form $\langle\psi,\Phi(X)\chi\rangle=\int_{U_n}\langle\psi_U,\phi(U^*XU)\chi_U\rangle\,d\mu(U)$.
--
--   Let $K\subseteq H$ be a complex subspace with $V(W)K\subseteq K$ for every $W\in U_n$, and let $b_1,\dots,b_d$ be an orthonormal basis of $K$. Define the compressed map $\Psi:M_n(\mathbb C)\to M_d(\mathbb C)$ by
--
--   $$\Psi(X)_{ij}=\langle b_i,\Phi(X)\,b_j\rangle\qquad(1\le i,j\le d),$$
--
--   the matrix of $P_K\Phi(X)P_K$ in the basis $(b_i)$. Then:
--
--   1. $\Psi$ is linear and unitarily equivariant: for every unitary $U\in U_n$ there is a unitary $V\in U_d$ with $\Psi(UXU^*)=V\Psi(X)V^*$ for all $X$;
--   2. if $\phi$ is $t$-positive, then so is $\Psi$;
--   3. for every $m$, $S_m(\Phi)\subseteq S_m(\Psi)$: every density matrix $\rho$ on $\mathbb C^m\otimes\mathbb C^n$ with $(i_m\otimes\Phi)(\rho)\ge0$ also has $(i_m\otimes\Psi)(\rho)\ge0$.
--
--   In the proof of Theorem 5.1 this is applied to the finite dimensional subspaces $H_d=P_dH$; items 1 and 2 are the source's claims on pp. 14–15 that $\Phi_d$ is $t$-positive and $\Pi_d$-equivariant, and item 3 is the monotonicity that makes the detection sets of the compressions decrease.
--
--   **Formalization Note** The compressed map is identified by its matrix entries, so the existential only carries linearity. Item 3 is a labelled addition to the printed claim, used by the goal for the decreasing family. Invariance is assumed under all $V(W)$, which with finite dimension makes the restriction of $V(W)$ to $K$ unitary. The form is a Bochner integral; with $\mu$ finite and $\psi,\chi\in L^2$ its integrand is integrable because the kernel $\phi(U^*XU)$ is bounded on $U_n$, so the integral's junk value $0$ does not arise. Bipartite matrices are indexed ancilla first, by $\{1..m\}\times\{1..n\}$, and $\Phi$ acts on the second factor.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, pp. 14–15, proof of Theorem 5.1 (the maps Φ_d = P_d Φ(·) P_d and the representation Π_d)

import Definitions.Def_EquivMapsEnt_Detect_Lift

namespace EquivMapsEnt.Detect

open MeasureTheory
open scoped Matrix ComplexOrder

/-- Proof of Theorem 5.1 (pp. 14–15): compressing the lift of equation (23) to a
finite-dimensional subspace invariant under the regular action gives a unitarily
equivariant matrix map, `t`-positive when `φ` is, which detects every state the lift detects. -/
theorem compression {n N d : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    [μ.IsMulLeftInvariant] [IsFiniteMeasure μ] (t m : ℕ)
    (K : Submodule ℂ (LiftSpace n N μ))
    (hK : ∀ (W : Matrix.unitaryGroup (Fin n) ℂ) (ψ : LiftSpace n N μ),
      ψ ∈ K → regRep μ W ψ ∈ K)
    (b : OrthonormalBasis (Fin d) ℂ K) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ,
      (∀ (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin d),
        Ψ X i j = liftForm φ μ X (b i : LiftSpace n N μ) (b j : LiftSpace n N μ)) ∧
      IsUnitarilyEquivariant Ψ ∧
      (IsTPositive t φ → IsTPositive t Ψ) ∧
      detectionSetLift m φ μ ⊆ detectionSet m Ψ := by sorry

end EquivMapsEnt.Detect
