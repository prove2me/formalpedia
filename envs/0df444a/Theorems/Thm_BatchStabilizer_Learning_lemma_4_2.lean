-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_4_2
-- name    : BatchStabilizer.Learning.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:03.925733+00:00
-- url     : https://prove2.me/theorems/2c9752a6-c414-4ffa-a683-8dc47e57464b
-- title:
--   Lemma 4.2 — syndrome Parseval identity
-- statement:
--   Let $T\subseteq\mathbb F_2^{2n}$ be an $r$-dimensional isotropic subspace, $b_1,\dots,b_r$ a basis of $T$, and $G_j=(-1)^{c_j}W_{b_j}$ Hermitian generators (any signs $c$). For a density matrix $\rho$ let $p_s=\operatorname{tr}(\rho\Pi_s)$ be the syndrome distribution of the joint measurement of $G_1,\dots,G_r$. Then
--   $$\sum_{s\in\mathbb F_2^r}p_s^2=\frac1{|T|}\sum_{t\in T}\big(\operatorname{tr}(\rho W_t)\big)^2.$$
--   The left side is the syndrome collision probability of two independent copies.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: the Pauli expectation tr(ρW_u) → the real part (ρ * W u).trace.re (pauliExp); reason: tr(ρW_u) is real for Hermitian ρ and Hermitian W_u, so nothing changes
--   - encoding: a stabilizer group S = ⟨G₁,…,G_r⟩ whose generators have labels forming a basis of T → generators G_j = (-1)^{c_j} W_{b_j} for a basis b of T and arbitrary signs c, with Π_s the ordered product (30); reason: the Hermitian Paulis with label b_j are exactly ±W_{b_j}; the factors commute because T is isotropic
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 13 (PDF p. 14), Lemma 4.2, equation (49)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Bell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 4.2, printed p. 13 (PDF p. 14): the syndrome Parseval identity (49), for any
Hermitian generators `G_j = (-1)^{c_j} W_{b_j}` whose labels form a basis of the isotropic `T`. -/
theorem lemma_4_2 {n r : ℕ} (ρ : Op (Qubits n)) (hρ : IsDensity ρ)
    (T : Submodule (ZMod 2) (Label n)) (hT : IsIsotropic T) (b : Fin r → Label n)
    (hb : IsLabelBasis T b) (c : Fin r → ZMod 2) :
    ∑ s : Fin r → ZMod 2, syndromeProb ρ b c s ^ 2 = pauliPowerSum ρ T / (Nat.card T : ℝ) := by sorry

end BatchStabilizer.Learning
