-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_corollary_5_6
-- name    : BatchStabilizer.Learning.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:50.624284+00:00
-- url     : https://prove2.me/theorems/3209557c-ea97-45be-a1ce-7dbb6047977d
-- title:
--   Corollary 5.6 — low-dimensional strongly biased Bell parities
-- statement:
--   In the analysis setup with $\sigma=U\rho U^\dagger$, suppose $F(\rho)\ge\tau>0$. Then the strongly biased subspace $V_{\rm bias}=\operatorname{span}\{x\neq0:|\tilde\beta_\sigma(x)|>\alpha/2\}$ satisfies
--   $$\dim V_{\rm bias}\le\frac{\log_2(\operatorname{tr}(\rho^2)/\alpha)}{\eta}\le\frac{2\log_2(1/\tau)}{\eta},\qquad\eta=1-H_2(1/4),$$
--   and for every $x\notin V_{\rm bias}$ and $b\in\mathbb F_2$,
--   $$\sum_{z:\,z\cdot x=b}\beta_\sigma((0,z))\le\frac{3\alpha}4 .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 20 (PDF p. 21), Corollary 5.6, equations (71)–(72)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Corollary 5.6, printed p. 20 (PDF p. 21): if `F(ρ) ≥ τ > 0`, the strongly biased subspace has
`dim V_bias ≤ log₂(tr(ρ²)/α)/η ≤ 2 log₂(1/τ)/η` (71), `η = 1 - H₂(1/4)`, and every `x ∉ V_bias`
and `b ∈ F₂` satisfy `Σ_{z·x=b} β_σ((0,z)) ≤ 3α/4` (72). -/
theorem corollary_5_6 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (τ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ) :
    (Module.finrank (ZMod 2) (Vbias (U * ρ * Uᴴ)) : ℝ) ≤
        Real.logb 2 (purity ρ / alpha (U * ρ * Uᴴ)) / eta ∧
      Real.logb 2 (purity ρ / alpha (U * ρ * Uᴴ)) / eta ≤ 2 * Real.logb 2 (1 / τ) / eta ∧
      ∀ x : Fin n → ZMod 2, x ∉ Vbias (U * ρ * Uᴴ) → ∀ b : ZMod 2,
        (∑ z : Fin n → ZMod 2, if z ⬝ᵥ x = b then bellProb (U * ρ * Uᴴ) (zLabel z) else 0) ≤
          3 * alpha (U * ρ * Uᴴ) / 4 := by sorry

end BatchStabilizer.Learning
