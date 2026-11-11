-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_7_1
-- name    : BatchStabilizer.Learning.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:25.437827+00:00
-- url     : https://prove2.me/theorems/833fce64-1d0d-4409-a77a-d7823373557a
-- title:
--   Lemma 7.1 — the shared Bell sumset spans the target
-- statement:
--   Let $\rho$ be a density matrix with $F(\rho)\ge\tau>0$, $T$ the label space of an optimal stabilizer state, and $0<\delta<1$. Let $B_3$ consist of $m_3=\lceil((n+1)\ln2+\ln(8/\delta))/(\kappa\tau^2)\rceil$ independent Bell outcomes and $U=\{m_i+m_j:1\le i<j\le m_3\}$. Then with probability at least $1-\delta/8$,
--   $$\operatorname{span}(U\cap T)=T .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: the label space T of a fixed optimal stabilizer state |ϕ*⟩ → labelSpace P for a projector P with IsOptimalStab ρ P (P ∈ Stab_n and tr(ρP) = F(ρ)); reason: states are compared as projectors; the span of the stabilizing labels of a stabilizer projector is its label space
--   - generalization: 0 < τ ≤ 1/2 with F(ρ) ≥ τ (the range of Theorem 1.1) → any τ > 0 with τ ≤ F(ρ); reason: a larger parameter range; it specializes to the source's range
--   - generalization: 0 < δ < 1/3 (the range of Theorem 1.1, in force throughout §§7–9) → 0 < δ < 1; reason: a larger parameter range; it specializes to the source's range
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 26 (PDF p. 27), Lemma 7.1, equations (85)–(86)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 7.1, printed p. 26 (PDF p. 27): for a batch `B₃` of `m₃` independent Bell outcomes
(85), the sumset `U = {m_i + m_j : i < j}` satisfies `span(U ∩ T) = T` (86) with probability
at least `1 - δ/8`. -/
theorem lemma_7_1 {n : ℕ} (ρ P : Op (Qubits n)) (hρ : IsDensity ρ) (hP : IsOptimalStab ρ P)
    (τ δ : ℝ) (hτ : 0 < τ) (hF : τ ≤ stabFidelity ρ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 8 ≤ bellBatchProb ρ (m3 n τ δ) (fun B3 =>
      Submodule.span (ZMod 2) ((↑(sumsetPairs B3) : Set (Label n)) ∩ ↑(labelSpace P)) =
        labelSpace P) := by sorry

end BatchStabilizer.Learning
