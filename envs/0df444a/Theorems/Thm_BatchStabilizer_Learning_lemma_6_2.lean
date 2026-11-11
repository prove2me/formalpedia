-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_6_2
-- name    : BatchStabilizer.Learning.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:06.801808+00:00
-- url     : https://prove2.me/theorems/4f3447d4-9a09-4072-84fa-de95fb06fa69
-- title:
--   Lemma 6.2 — separating the biased subspace
-- statement:
--   Assume the analysis setup with $0<\tau<1$ and $F(\rho)\ge\tau$, fix an anchor $a\in A_T$, and let $B_2$ consist of $m_2$ independent Bell records. Then $d=\dim V_{\rm bias}\le k_2$, and with probability at least $0.99$ there are $d$ distinct records $m_1,\dots,m_d\in B_2\cap A_T$, with $C(m_j+a)=(0,w_j)$, such that every nonzero $v\in V_{\rm bias}$ has
--   $$w_j\cdot v=1\quad\text{for some }1\le j\le d .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - reading: there exist d records m₁,…,m_d ∈ B₂ ∩ A_T → an injective choice of d record indices of B₂, all in A_T; reason: records are entries of the batch; d records means d distinct entries, the stronger reading
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 24 (PDF p. 25), Lemma 6.2, equation (77)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 6.2, printed p. 24 (PDF p. 25): fix an anchor `a ∈ A_T` and a batch `B₂` of `m₂`
independent Bell records.  Then `d = dim V_bias ≤ k₂`, and with probability at least `0.99` there
are `d` records `m_1,…,m_d ∈ B₂ ∩ A_T`, `C(m_j + a) = (0, w_j)`, such that every nonzero
`v ∈ V_bias` has `w_j · v = 1` for some `j` (77). -/
theorem lemma_6_2 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hF : τ ≤ stabFidelity ρ)
    (a : Label n) (ha : a ∈ affineFilter (labelSpace P)) :
    Module.finrank (ZMod 2) (Vbias (U * ρ * Uᴴ)) ≤ k2 τ ∧
      (99 / 100 : ℝ) ≤ bellBatchProb ρ (m2 τ) (fun B2 =>
        ∃ f : Fin (Module.finrank (ZMod 2) (Vbias (U * ρ * Uᴴ))) → Fin (m2 τ),
          Function.Injective f ∧ (∀ j, B2 (f j) ∈ affineFilter (labelSpace P)) ∧
          ∀ v ∈ Vbias (U * ρ * Uᴴ), v ≠ 0 → ∃ j, (C (B2 (f j) + a)).2 ⬝ᵥ v = 1) := by sorry

end BatchStabilizer.Learning
