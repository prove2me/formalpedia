-- Prove2me | Theorems.Thm_EquivMapsEnt_Detect_theorem_5_2
-- name    : EquivMapsEnt.Detect.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:47.328979+00:00
-- url     : https://prove2.me/theorems/965429f6-317c-4d30-9815-5ba5919dbcbc
-- title:
--   Theorem 5.2: the fibrewise lift is unitarily equivariant, t-positive, and detects every state detected by the input map
-- statement:
--   Let $t,m\ge 0$ and let $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$ be a $t$-positive linear map. Let $\mu$ be a finite, left-invariant Borel measure on $U_n$ assigning positive mass to every nonempty open set (the Haar measure is one), let $H=L^2(U_n,\mathbb C^N;\mu)$, let $V(W)\psi=(\psi_{W^*U})_{U}$ be the left regular representation of eq. (22), and let $\Phi$ be the fibrewise lift of eq. (23), $\Phi(X)\psi=(\phi(U^*XU)\psi_U)_U$. Then each $V(W)$ is a unitary of $H$ (an isometry that is onto),
--   $$V(W)^*\,\Phi(WXW^*)\,V(W)=\Phi(X)\quad\text{for all }W\in U_n,\ X\in M_n(\mathbb C),$$
--   $\Phi$ is $t$-positive, and
--   $$S_m(\Phi)\subseteq S_m(\phi).$$
--
--   So the Hilbert space and the unitarily equivariant $t$-positive map whose existence the theorem asserts are the explicit ones of equations (21)–(23). This is the infinite dimensional step of the proof of Theorem 5.1.
--
--   **Formalization Note** The witness is made explicit rather than existentially quantified, which is stronger than the printed existence statement. Operators on $H$ are encoded by their sesquilinear forms $\langle\psi,\Phi(X)\chi\rangle$ (`liftForm`); $t$-positivity and $S_m(\Phi)$ are the corresponding quadratic-form conditions on $\mathbb C^t\otimes H$ and $\mathbb C^m\otimes H$, with the ancilla first. The equivariance identity is stated on forms. The measure is a parameter carrying the properties of the Haar measure the proof uses; finiteness and $L^2$ membership make every integrand integrable, so Lean's zero value of a non-integrable Bochner integral does not arise.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, p. 13, Theorem 5.2 and equation (19) (proof p. 14)

import Definitions.Def_EquivMapsEnt_Detect_Lift

namespace EquivMapsEnt.Detect

open MeasureTheory
open scoped Matrix ComplexOrder

/-- Theorem 5.2, with its explicit witness from equations (21)–(23): the lift is unitarily
equivariant for the unitary representation `regRep`, `t`-positive, and detects every state that
`φ` detects. -/
theorem theorem_5_2 (m t : ℕ) {n N : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hφ : IsTPositive t φ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    [μ.IsMulLeftInvariant] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    (∀ W : Matrix.unitaryGroup (Fin n) ℂ,
      Function.Surjective (regRep (N := N) μ W)) ∧
    (∀ (W : Matrix.unitaryGroup (Fin n) ℂ)
      (X : Matrix (Fin n) (Fin n) ℂ) (ψ χ : LiftSpace n N μ),
      liftForm φ μ ((W : Matrix (Fin n) (Fin n) ℂ) * X * star (W : Matrix (Fin n) (Fin n) ℂ))
        (regRep μ W ψ) (regRep μ W χ) = liftForm φ μ X ψ χ) ∧
    IsTPositiveLift t φ μ ∧
    detectionSetLift m φ μ ⊆ detectionSet m φ := by sorry

end EquivMapsEnt.Detect
