-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_8_2
-- name    : BatchStabilizer.Learning.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:46.150529+00:00
-- url     : https://prove2.me/theorems/fd99f7d3-e48c-4405-92be-b61e25c5be5f
-- title:
--   Lemma 8.2 — few representative stabilizer bases
-- statement:
--   Let $\rho$ be a density matrix, $\tau>0$, $t=\lceil\log_2(8/\tau^4)\rceil$, and let $\mathcal L_{\rm cert}$ be a list of full isotropic subspaces on the event of Lemma 8.1, i.e. each with $\Pr(M\in A_{T'})>\tau^2/2$. Then the greedy representative family $\mathcal R\subseteq\mathcal L_{\rm cert}$, built by binary linear algebra, satisfies $|\mathcal R|\le4/\tau^2$, and every $T'\in\mathcal L_{\rm cert}$ has some $T_i\in\mathcal R$ with
--   $$\dim(T'\cap T_i)\ge n-t .$$
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: on the event guaranteed by Lemma 8.1; there exists ℛ, found by a greedy algorithm → hypotheses that each listed T' is full isotropic with Pr(M ∈ A_{T'}) > τ²/2; the conclusion is stated for the defined greedy family; reason: these are the properties of ℒ_cert on that event; the defined greedy family witnesses the existence
--   - encoding: n − t → integer subtraction (n : ℤ) − t; reason: t may exceed n; the source's n − t is an integer
--   - generalization: 0 < τ ≤ 1/2 (Theorem 1.1) → any τ > 0; reason: a larger range; it specializes to the source's range
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 34 (PDF p. 35), Lemma 8.2

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Algorithms

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 8.2, printed p. 34 (PDF p. 35): on the event of Lemma 8.1 (every certified full
isotropic `T'` has `Pr(M ∈ A_{T'}) > τ²/2`), with `t = ⌈log₂(8/τ⁴)⌉`, the greedy maximal family
`ℛ ⊆ ℒ_cert` (computed by binary linear algebra) has `|ℛ| ≤ 4/τ²`, and every `T' ∈ ℒ_cert` has
some `T_i ∈ ℛ` with `dim(T' ∩ T_i) ≥ n - t`. -/
theorem lemma_8_2 {n : ℕ} (ρ : Op (Qubits n)) (hρ : IsDensity ρ) (τ : ℝ) (hτ : 0 < τ)
    (cert : List (Sub n)) (hfull : ∀ T' ∈ cert, IsFull T')
    (hE : ∀ T' ∈ cert, τ ^ 2 / 2 < energy ρ T') :
    (∀ Ti ∈ greedyReps n (tt τ) cert, Ti ∈ cert) ∧
      ((greedyReps n (tt τ) cert).length : ℝ) ≤ 4 / τ ^ 2 ∧
      ∀ T' ∈ cert, ∃ Ti ∈ greedyReps n (tt τ) cert,
        (n : ℤ) - tt τ ≤ (Module.finrank (ZMod 2) ↥(T' ⊓ Ti) : ℤ) := by sorry

end BatchStabilizer.Learning
