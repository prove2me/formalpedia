-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_5_2
-- name    : BatchStabilizer.Learning.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:42.406436+00:00
-- url     : https://prove2.me/theorems/afd39877-67e1-4499-90b2-8063a53616a0
-- title:
--   Lemma 5.2 — sharp mixed-state Fourier gap
-- statement:
--   In the analysis setup ($P=|\phi^*\rangle\langle\phi^*|$ optimal, $U$ a Clifford with $U|\phi^*\rangle\propto|0^n\rangle$, $\sigma=U\rho U^\dagger$, $\alpha=\sum_x\sigma_{x,x}^2$), every nonzero $x\in\mathbb F_2^n$ satisfies $\tilde\beta_\sigma(x)=\sum_{y}\sigma_{y,y+x}^2$, a real number (the complex entries are squared, not their moduli), and
--   $$\alpha-|\tilde\beta_\sigma(x)|\ge2\kappa F(\rho)^2,\qquad\kappa=6-4\sqrt2 .$$
--   The constant is sharp. The gap shows that both parity values of every nontrivial check occur among target-coset Bell outcomes.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - encoding: β̃_σ(x) = Σ_y σ_{y,y+x}² ∈ ℝ → the complex cast of the real number β̃_σ(x) equals the complex sum Σ_y σ_{y,y+x}²; reason: equality with a real cast states both the formula and its reality
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 17 (PDF p. 18), Lemma 5.2, equation (62)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 5.2, printed p. 17 (PDF p. 18): for the optimal target and `σ = UρU†`, every nonzero
`x` has `β̃_σ(x) = Σ_y σ_{y,y+x}² ∈ ℝ` and the sharp gap `α - |β̃_σ(x)| ≥ 2κF(ρ)²` (62),
`κ = 6 - 4√2`. -/
theorem lemma_5_2 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (x : Fin n → ZMod 2) (hx : x ≠ 0) :
    ((tildeBeta (U * ρ * Uᴴ) x : ℝ) : ℂ) =
        ∑ y : Fin n → ZMod 2, (U * ρ * Uᴴ) (toQubits y) (toQubits (y + x)) ^ 2 ∧
      2 * kappa * stabFidelity ρ ^ 2 ≤ alpha (U * ρ * Uᴴ) - |tildeBeta (U * ρ * Uᴴ) x| := by sorry

end BatchStabilizer.Learning
