-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_4_1
-- name    : BatchStabilizer.Learning.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:02.836216+00:00
-- url     : https://prove2.me/theorems/3f268190-4c30-473d-87bc-3955430ced35
-- title:
--   Lemma 4.1 — mixed-state Bell Fourier identity and pointwise bound
-- statement:
--   Let $\rho$ be any $n$-qubit density matrix and $\beta_\rho$ its Bell distribution. Then for every $m\in\mathbb F_2^{2n}$
--   $$\beta_\rho(m)=\frac1{4^n}\sum_{u\in\mathbb F_2^{2n}}(-1)^{Q(u)+\langle m,u\rangle}\big(\operatorname{tr}(\rho W_u)\big)^2,$$
--   equivalently its symplectic Fourier coefficients are $\hat\beta_\rho(u)=(-1)^{Q(u)}(\operatorname{tr}\rho W_u)^2$, and moreover
--   $$0\le\beta_\rho(m)\le\frac{\operatorname{tr}(\rho^2)}{2^n}\le\frac1{2^n}.$$
--   The powers are squares of real Pauli expectations; the sign $(-1)^{Q(u)}$ comes from Pauli transposition. This identity is the basis of every Bell-sampling statistic in the mission.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: the Pauli expectation tr(ρW_u) → the real part (ρ * W u).trace.re (pauliExp); reason: tr(ρW_u) is real for Hermitian ρ and Hermitian W_u, so nothing changes
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 12 (PDF p. 13), Lemma 4.1, equations (40)–(43)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Bell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 4.1, printed p. 12 (PDF p. 13): the mixed-state Bell Fourier identity (40), its
Fourier form (41)–(42), and the pointwise bound (43). -/
theorem lemma_4_1 {n : ℕ} (ρ : Op (Qubits n)) (hρ : IsDensity ρ) :
    (∀ m : Label n, bellProb ρ m =
      (1 / 4 ^ n : ℝ) * ∑ u : Label n, signZ (Q u + symp m u) * pauliExp ρ u ^ 2) ∧
    (∀ u : Label n, bellFourier ρ u = signZ (Q u) * pauliExp ρ u ^ 2) ∧
    (∀ m : Label n, 0 ≤ bellProb ρ m ∧ bellProb ρ m ≤ purity ρ / 2 ^ n ∧
      purity ρ / 2 ^ n ≤ 1 / 2 ^ n) := by sorry

end BatchStabilizer.Learning
