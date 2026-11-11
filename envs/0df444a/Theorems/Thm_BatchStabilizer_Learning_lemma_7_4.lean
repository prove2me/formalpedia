-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_7_4
-- name    : BatchStabilizer.Learning.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:53.520027+00:00
-- url     : https://prove2.me/theorems/d55552c2-db1d-4acc-9a4c-cbfdf9b582ad
-- title:
--   Lemma 7.4 — a good seed gives the 9/11 versus 2/11 gap
-- statement:
--   In the analysis setup with $F(\rho)\ge\tau>0$, suppose $L\subseteq T$ and $\Delta(L)\le\tau^2/10$. Then for every $u\in L^\perp$,
--   $$\gamma_L(u)\ge\frac9{11}\ \text{ if }u\in T,\qquad\gamma_L(u)\le\frac2{11}\ \text{ if }u\notin T .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - generalization: 0 < τ ≤ 1/2 with F(ρ) ≥ τ (the range of Theorem 1.1) → any τ > 0 with τ ≤ F(ρ); reason: a larger parameter range; it specializes to the source's range
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 29 (PDF p. 30), Lemma 7.4, equation (94)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 7.4, printed p. 29 (PDF p. 30): if `L ⊆ T` and `Δ(L) ≤ τ²/10` (with `F(ρ) ≥ τ > 0`),
then every `u ∈ L^⊥` has `γ_L(u) ≥ 9/11` when `u ∈ T` and `γ_L(u) ≤ 2/11` when `u ∉ T` (94). -/
theorem lemma_7_4 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (τ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ)
    (L : Submodule (ZMod 2) (Label n)) (hLT : L ≤ labelSpace P)
    (hΔ : collisionExcess (U * ρ * Uᴴ) C L ≤ τ ^ 2 / 10) :
    ∀ u ∈ perp L, (u ∈ labelSpace P → (9 / 11 : ℝ) ≤ condScore ρ L u) ∧
      (u ∉ labelSpace P → condScore ρ L u ≤ 2 / 11) := by sorry

end BatchStabilizer.Learning
