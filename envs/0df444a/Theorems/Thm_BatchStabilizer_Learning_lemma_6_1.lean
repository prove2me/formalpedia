-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_6_1
-- name    : BatchStabilizer.Learning.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:40.169296+00:00
-- url     : https://prove2.me/theorems/839eb90c-14ca-49fe-b195-1a917ab64f7c
-- title:
--   Lemma 6.1 — collision reduction outside the biased subspace
-- statement:
--   Assume the analysis setup with $0<\tau<1$ and $F(\rho)\ge\tau$, and fix an anchor $a\in A_T$. Let $B_1$ be a batch of $m_1$ independent Bell records, $N_{\rm hit}$ the number of its records in $A_T$, and, when $N_{\rm hit}\ge k_1$, let $m_1,\dots,m_{k_1}$ be the first $k_1$ such records with $C(m_j+a)=(0,z_j)$. Conditioned on $N_{\rm hit}\ge k_1$, with probability at least $0.9$,
--   $$\sum_{\substack{x\neq y,\ x+y\notin V_{\rm bias}\\ z_j\cdot(x+y)=0\ \forall j}}p_xp_y\le\frac{\tau^2}{10}.$$
--   The conditional probability is expressed as $\Pr(N_{\rm hit}\ge k_1\text{ and the bound})\ge0.9\Pr(N_{\rm hit}\ge k_1)$.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - encoding: the conditional probability given a and N_hit ≥ k₁ → Pr_{B₁}(N_hit ≥ k₁ ∧ (75)) ≥ 0.9 · Pr_{B₁}(N_hit ≥ k₁) for the fixed anchor a; reason: B₁ is independent of the anchor; the inequality is the conditional statement when Pr(N_hit ≥ k₁) > 0
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 23 (PDF p. 24), Lemma 6.1, equation (75)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

open Classical in
/-- Lemma 6.1, printed p. 23 (PDF p. 24): fix an anchor `a ∈ A_T`; let `N_hit` be the number of
records of the batch `B₁` (of `m₁` independent Bell records) in `A_T`, and for the first `k₁`
such records write `C(m_j + a) = (0, z_j)`.  Conditioned on `N_hit ≥ k₁`, with probability at
least `0.9` the unseparated weight outside `V_bias` is at most `τ²/10` (75).  The conditional
probability is written as `Pr(N_hit ≥ k₁ ∧ (75)) ≥ 0.9 · Pr(N_hit ≥ k₁)`. -/
theorem lemma_6_1 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hF : τ ≤ stabFidelity ρ)
    (a : Label n) (ha : a ∈ affineFilter (labelSpace P)) :
    (9 / 10 : ℝ) *
        bellBatchProb ρ (m1 τ) (fun B1 => k1 τ ≤ (accepted (labelSpace P) B1).length) ≤
      bellBatchProb ρ (m1 τ) (fun B1 => k1 τ ≤ (accepted (labelSpace P) B1).length ∧
        (∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          if x ≠ y ∧ x + y ∉ Vbias (U * ρ * Uᴴ) ∧
              ∀ j ∈ (accepted (labelSpace P) B1).take (k1 τ), (C (B1 j + a)).2 ⬝ᵥ (x + y) = 0
          then compProb (U * ρ * Uᴴ) x * compProb (U * ρ * Uᴴ) y else 0) ≤ τ ^ 2 / 10) := by sorry

end BatchStabilizer.Learning
