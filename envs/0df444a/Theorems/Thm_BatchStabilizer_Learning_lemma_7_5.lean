-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_7_5
-- name    : BatchStabilizer.Learning.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:31.47345+00:00
-- url     : https://prove2.me/theorems/877569a0-89ab-4015-8042-d50e24db029b
-- title:
--   Lemma 7.5 — correctness of batchwise extension
-- statement:
--   In the analysis setup with $F(\rho)\ge\tau>0$ and $0<\delta<1$, let a seed list $\mathcal L$ contain a good seed $L\subseteq T$ with $\Delta(L)\le\tau^2/10$, and let the Bell sumset $U$ satisfy $\operatorname{span}(U\cap T)=T$. Then, with probability at least $1-\delta/4$ over the independent Bell batch $B_4$ of $m_4$ records, Algorithm 2 returns a list containing $T$.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - generalization: 0 < τ ≤ 1/2 with F(ρ) ≥ τ (the range of Theorem 1.1) → any τ > 0 with τ ≤ F(ρ); reason: a larger parameter range; it specializes to the source's range
--   - generalization: 0 < δ < 1/3 (the range of Theorem 1.1, in force throughout §§7–9) → 0 < δ < 1; reason: a larger parameter range; it specializes to the source's range
--   - generalization: conditional on the earlier measurement batches (the lists produced by the previous stages) → every fixed list (or set) satisfying the stated hypotheses, with probability over the fresh independent batch only; reason: conditioning on the earlier batches fixes these inputs; a statement for every fixed input specializes to the conditional one
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 30 (PDF p. 31), Lemma 7.5

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 7.5, printed p. 30 (PDF p. 31): if the (fixed) seed list contains a good seed `L ⊆ T`
with `Δ(L) ≤ τ²/10` and the (fixed) sumset satisfies `span(U ∩ T) = T`, then over the
independent batch `B₄` Algorithm 2 returns a list containing `T` with probability at least
`1 - δ/4`. -/
theorem lemma_7_5 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (τ δ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (seeds : List (Sub n)) (S : Finset (Label n))
    (hgood : ∃ L ∈ seeds, L ≤ labelSpace P ∧ collisionExcess (U * ρ * Uᴴ) C L ≤ τ ^ 2 / 10)
    (hspan : Submodule.span (ZMod 2) ((↑S : Set (Label n)) ∩ ↑(labelSpace P)) = labelSpace P) :
    1 - δ / 4 ≤ bellBatchProb ρ (m4 τ δ seeds.length S.card)
      (fun B4 => labelSpace P ∈ extend τ δ seeds S B4) := by sorry

end BatchStabilizer.Learning
