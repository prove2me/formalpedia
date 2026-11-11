-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_corollary_5_3
-- name    : BatchStabilizer.Learning.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:22.092298+00:00
-- url     : https://prove2.me/theorems/00281667-da0f-4329-a955-88840a66e22f
-- title:
--   Corollary 5.3 — escape from every proper target subspace
-- statement:
--   Let $\rho$ be a density matrix, $T$ the label space of an optimal stabilizer state $|\phi^*\rangle$, and $a\in A_T$ any anchor. For every proper linear subspace $V\subsetneq T$,
--   $$\Pr_{M\sim\beta_\rho}\big(M\in A_T,\ M+a\notin V\big)\ge\kappa F(\rho)^2 .$$
--   This is the rank-growth step used by the seed-listing and sumset lemmas.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: the label space T of a fixed optimal stabilizer state |ϕ*⟩ → labelSpace P for a projector P with IsOptimalStab ρ P (P ∈ Stab_n and tr(ρP) = F(ρ)); reason: states are compared as projectors; the span of the stabilizing labels of a stabilizer projector is its label space
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 19 (PDF p. 20), Corollary 5.3, equation (66)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Corollary 5.3, printed p. 19 (PDF p. 20): for the label space `T` of an optimal stabilizer
state, every anchor `a ∈ A_T`, and every proper subspace `V ⊊ T`,
`Pr_{M∼β_ρ}(M ∈ A_T, M + a ∉ V) ≥ κF(ρ)²` (66). -/
theorem corollary_5_3 {n : ℕ} (ρ P : Op (Qubits n)) (hρ : IsDensity ρ) (hP : IsOptimalStab ρ P)
    (a : Label n) (ha : a ∈ affineFilter (labelSpace P))
    (V : Submodule (ZMod 2) (Label n)) (hV : V < labelSpace P) :
    kappa * stabFidelity ρ ^ 2 ≤
      bellEventProb ρ {m | m ∈ affineFilter (labelSpace P) ∧ m + a ∉ V} := by sorry

end BatchStabilizer.Learning
