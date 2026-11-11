-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_8_1
-- name    : BatchStabilizer.Learning.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:48.316748+00:00
-- url     : https://prove2.me/theorems/769c8ab0-e48a-48d2-a2f5-9fa4fdd80319
-- title:
--   Lemma 8.1 — independent energy certification
-- statement:
--   Let $\rho$ be a density matrix with $F(\rho)\ge\tau>0$, $T$ the label space of an optimal stabilizer state, $0<\delta<1$, and $\mathcal L_{\rm full}$ a fixed candidate list. With probability at least $1-\delta/8$ over the independent batch $B_5$ of $m_5$ Bell records, Algorithm 3 retains every $T'\in\mathcal L_{\rm full}$ with $\Pr(M\in A_{T'})\ge\tau^2$ and rejects every candidate with $\Pr(M\in A_{T'})\le\tau^2/2$; in particular, if $T\in\mathcal L_{\rm full}$ then $T\in\mathcal L_{\rm cert}$, and every retained candidate satisfies
--   $$\Pr(M\in A_{T'})>\tau^2/2 .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: the label space T of a fixed optimal stabilizer state |ϕ*⟩ → labelSpace P for a projector P with IsOptimalStab ρ P (P ∈ Stab_n and tr(ρP) = F(ρ)); reason: states are compared as projectors; the span of the stabilizing labels of a stabilizer projector is its label space
--   - generalization: 0 < τ ≤ 1/2 with F(ρ) ≥ τ (the range of Theorem 1.1) → any τ > 0 with τ ≤ F(ρ); reason: a larger parameter range; it specializes to the source's range
--   - generalization: 0 < δ < 1/3 (the range of Theorem 1.1, in force throughout §§7–9) → 0 < δ < 1; reason: a larger parameter range; it specializes to the source's range
--   - generalization: conditional on the earlier measurement batches (the lists produced by the previous stages) → every fixed list (or set) satisfying the stated hypotheses, with probability over the fresh independent batch only; reason: conditioning on the earlier batches fixes these inputs; a statement for every fixed input specializes to the conditional one
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 32–33 (PDF p. 33–34), Lemma 8.1, equation (99)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 8.1, printed pp. 32–33 (PDF pp. 33–34): for any fixed candidate list `ℒ_full`, with
probability at least `1 - δ/8` over the independent batch `B₅`, Algorithm 3 retains every
candidate with `Pr(M ∈ A_{T'}) ≥ τ²` and rejects every candidate with `Pr(M ∈ A_{T'}) ≤ τ²/2`;
in particular `T ∈ ℒ_full` implies `T ∈ ℒ_cert`, and every retained candidate has
`Pr(M ∈ A_{T'}) > τ²/2` (99). -/
theorem lemma_8_1 {n : ℕ} (ρ P : Op (Qubits n)) (hρ : IsDensity ρ) (hP : IsOptimalStab ρ P)
    (τ δ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (full : List (Sub n)) :
    1 - δ / 8 ≤ bellBatchProb ρ (m5 τ δ full.length) (fun B5 =>
      (∀ T' ∈ full, τ ^ 2 ≤ energy ρ T' → T' ∈ certify τ δ full B5) ∧
      (∀ T' ∈ full, energy ρ T' ≤ τ ^ 2 / 2 → T' ∉ certify τ δ full B5) ∧
      (labelSpace P ∈ full → labelSpace P ∈ certify τ δ full B5) ∧
      ∀ T' ∈ certify τ δ full B5, τ ^ 2 / 2 < energy ρ T') := by sorry

end BatchStabilizer.Learning
