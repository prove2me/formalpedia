-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_7_3
-- name    : BatchStabilizer.Learning.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:07.283283+00:00
-- url     : https://prove2.me/theorems/ac7118ba-cc48-429b-a843-d2de8f608ca7
-- title:
--   Lemma 7.3 — conditional score formula, range and uncertainty
-- statement:
--   Let $\rho$ be a density matrix, $L$ an isotropic subspace and $u\in L^\perp$. Then
--   $$\gamma_L(u)=\frac{\sum_{t\in L}(\operatorname{tr}\rho W_{u+t})^2}{\sum_{t\in L}(\operatorname{tr}\rho W_t)^2},$$
--   in particular $0\le\gamma_L(u)\le1$; moreover, if $u,v\in L^\perp$ label anticommuting Paulis ($\langle u,v\rangle=1$), then $\gamma_L(u)+\gamma_L(v)\le1$.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: the Pauli expectation tr(ρW_u) → the real part (ρ * W u).trace.re (pauliExp); reason: tr(ρW_u) is real for Hermitian ρ and Hermitian W_u, so nothing changes
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 28 (PDF p. 29), Lemma 7.3, equations (92)–(93)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Bell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

open Classical in
/-- Lemma 7.3, printed p. 28 (PDF p. 29): for isotropic `L` and `u ∈ L^⊥`,
`γ_L(u) = Σ_{t∈L} tr(ρW_{u+t})² / Σ_{t∈L} tr(ρW_t)²` (92), `0 ≤ γ_L(u) ≤ 1`, and
`γ_L(u) + γ_L(v) ≤ 1` whenever `u, v ∈ L^⊥` label anticommuting Paulis (93). -/
theorem lemma_7_3 {n : ℕ} (ρ : Op (Qubits n)) (hρ : IsDensity ρ)
    (L : Submodule (ZMod 2) (Label n)) (hL : IsIsotropic L) (u : Label n) (hu : u ∈ perp L) :
    condScore ρ L u =
        (∑ t : Label n, if t ∈ L then pauliExp ρ (u + t) ^ 2 else 0) / pauliPowerSum ρ L ∧
      0 ≤ condScore ρ L u ∧ condScore ρ L u ≤ 1 ∧
      ∀ v ∈ perp L, symp u v = 1 → condScore ρ L u + condScore ρ L v ≤ 1 := by sorry

end BatchStabilizer.Learning
