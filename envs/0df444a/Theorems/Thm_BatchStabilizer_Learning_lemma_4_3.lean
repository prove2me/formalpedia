-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_4_3
-- name    : BatchStabilizer.Learning.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:31.7718+00:00
-- url     : https://prove2.me/theorems/3c6bc434-df48-4e12-94e0-3c471bb2a0ef
-- title:
--   Lemma 4.3 — syndrome parity checks on Bell outcomes
-- statement:
--   Let $T$ be an $r$-dimensional isotropic subspace with basis $b$ and Hermitian generators $G_j=(-1)^{c_j}W_{b_j}$, and let $\rho$ be a density matrix. The probability that a two-copy Bell measurement lands in the affine filter $A_T$ satisfies
--   $$\Pr(M\in A_T)=\frac1{|T|}\sum_{t\in T}\big(\operatorname{tr}\rho W_t\big)^2=\sum_{s\in\mathbb F_2^r}p_s^2 .$$
--   Thus the energy $E(T)$ is measurable from Bell records without measuring the stabilizer generators.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: the Pauli expectation tr(ρW_u) → the real part (ρ * W u).trace.re (pauliExp); reason: tr(ρW_u) is real for Hermitian ρ and Hermitian W_u, so nothing changes
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: the syndrome distribution p_s of the stabilizer generators of T → p_s for generators G_j = (-1)^{c_j} W_{b_j}, b a basis of T, c arbitrary; reason: these are all Hermitian generator choices with labels forming a basis of T
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 14 (PDF p. 15), Lemma 4.3, equation (51)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Bell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 4.3, printed p. 14 (PDF p. 15): the Bell acceptance probability of the affine filter
`A_T` equals the average Pauli power over `T` and the syndrome collision probability (51). -/
theorem lemma_4_3 {n r : ℕ} (ρ : Op (Qubits n)) (hρ : IsDensity ρ)
    (T : Submodule (ZMod 2) (Label n)) (hT : IsIsotropic T) (b : Fin r → Label n)
    (hb : IsLabelBasis T b) (c : Fin r → ZMod 2) :
    energy ρ T = pauliPowerSum ρ T / (Nat.card T : ℝ) ∧
      pauliPowerSum ρ T / (Nat.card T : ℝ) = ∑ s : Fin r → ZMod 2, syndromeProb ρ b c s ^ 2 := by sorry

end BatchStabilizer.Learning
