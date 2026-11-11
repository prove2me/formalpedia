-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_6_3
-- name    : BatchStabilizer.Learning.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:17.589793+00:00
-- url     : https://prove2.me/theorems/08034ea0-cfc8-4c7e-8f12-6d7dd89bd473
-- title:
--   Lemma 6.3 — a good partial stabilizer is listed
-- statement:
--   Suppose $F(\rho)\ge\tau$ for some $0<\tau<1$, in the analysis setup. With probability at least $3/4$ over its batches $B_0,B_1,B_2$, the list produced by Algorithm 1 contains a subspace $L\subseteq T$ with
--   $$\dim L\le k=O(1+\ln(1/\tau)),\qquad\Delta(L)\le\tau^2/10 .$$
--   The algorithm uses $m_0+m_1+m_2=O(\tau^{-2}(1+\ln(1/\tau)))$ Bell outcomes and, on every transcript, outputs at most
--   $$m_0(1+m_1+m_2)^k=\exp\big(O((1+\ln(1/\tau))^2)\big)$$
--   candidate subspaces. The $O$-constants are a single absolute constant $K$, valid for all $0<\tau<1$.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - encoding: O(·) and exp(O(·)) bounds → one absolute constant K > 0, chosen before τ, bounding k, m₀+m₁+m₂ and m₀(1+m₁+m₂)^k; reason: the uniform meaning of the source's O-notation
--   - encoding: outputs at most m₀(1+m₁+m₂)^k candidate subspaces → the output list, counted with multiplicity, has length at most m₀(1+m₁+m₂)^k for every value of the records; reason: a bound with multiplicity bounds the number of distinct candidates
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 24 (PDF p. 25), Lemma 6.3, equations (79)–(81)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 6.3, printed p. 24 (PDF p. 25): if `F(ρ) ≥ τ` with `0 < τ < 1`, then with probability at
least `3/4` the list of Algorithm 1 contains `L ⊆ T` with `dim L ≤ k` (79) and `Δ(L) ≤ τ²/10`
(80); `k = O(1 + ln(1/τ))`; the algorithm uses `m₀ + m₁ + m₂ = O(τ⁻²(1 + ln(1/τ)))` Bell
outcomes; and it outputs at most `m₀(1 + m₁ + m₂)^k = exp(O((1 + ln(1/τ))²))` candidates (81).
The `O`-constant is absolute. -/
theorem lemma_6_3 :
    (∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 0 < τ → τ < 1 →
      (kk τ : ℝ) ≤ K * (1 + Real.log (1 / τ)) ∧
      ((m0 τ + m1 τ + m2 τ : ℕ) : ℝ) ≤ K * (1 + Real.log (1 / τ)) / τ ^ 2 ∧
      ((m0 τ * (1 + m1 τ + m2 τ) ^ kk τ : ℕ) : ℝ) ≤ Real.exp (K * (1 + Real.log (1 / τ)) ^ 2)) ∧
    (∀ (n : ℕ) (τ : ℝ) (B0 : Fin (m0 τ) → Label n) (B1 : Fin (m1 τ) → Label n)
        (B2 : Fin (m2 τ) → Label n),
      (seedList τ B0 B1 B2).length ≤ m0 τ * (1 + m1 τ + m2 τ) ^ kk τ) ∧
    (∀ (n : ℕ) (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n),
      TargetSetup ρ P U C → ∀ τ : ℝ, 0 < τ → τ < 1 → τ ≤ stabFidelity ρ →
        (3 / 4 : ℝ) ≤ (alg1Prog n τ).prob ρ (fun Ls => ∃ L ∈ Ls, L ≤ labelSpace P ∧
          Module.finrank (ZMod 2) L ≤ kk τ ∧ collisionExcess (U * ρ * Uᴴ) C L ≤ τ ^ 2 / 10)) := by sorry

end BatchStabilizer.Learning
