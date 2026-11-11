-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_4_4
-- name    : BatchStabilizer.Learning.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:43.169474+00:00
-- url     : https://prove2.me/theorems/f7823f06-1130-40aa-85bd-5e4efafd5d4b
-- title:
--   Lemma 4.4 — affine Clifford relabeling of Bell outcomes
-- statement:
--   Let $U$ be a unitary whose conjugation maps Hermitian Paulis to Hermitian Paulis up to sign, $UW_uU^\dagger=\pm W_{Cu}$, for a linear bijection $C$ of $\mathbb F_2^{2n}$. Then there is a unique $d_C\in\mathbb F_2^{2n}$ with
--   $$\langle d_C,v\rangle=Q(v)+Q(C^{-1}v)\quad\text{for all }v,$$
--   and for every density matrix $\rho$ and outcome $m$,
--   $$\beta_{U\rho U^\dagger}(m)=\beta_\rho\big(C^{-1}(m+d_C)\big);$$
--   moreover $CA_T+d_C=A_{CT}$ for every isotropic subspace $T$.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: β_ρ(m) = ⟨Φ_m|(ρ⊗ρ)|Φ_m⟩ → the real part of the same quadratic form, with |Φ_m⟩ entries 2^{-n/2}(W_m)_{x,y}; reason: the quadratic form of the positive semidefinite ρ⊗ρ is real
--   - encoding: a Clifford unitary U inducing the symplectic transformation C as in (53) → a unitary U and a linear equivalence C with U W_u U† = W_{Cu} or −W_{Cu} for all u; reason: (53) is the definition of C; a unitary with this property is a Clifford unitary
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 15 (PDF p. 16), Lemma 4.4, equations (54)–(56)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Lemma 4.4, printed p. 15 (PDF p. 16): Clifford conjugation relabels Bell outcomes by the
affine map `m ↦ C⁻¹(m + d_C)` (54), with `d_C` the unique solution of (55), and maps
syndrome cosets as `C A_T + d_C = A_{CT}` (56). -/
theorem lemma_4_4 {n : ℕ} (U : Op (Qubits n)) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (C : Label n ≃ₗ[ZMod 2] Label n) (hC : IsSymplecticAction U C) :
    ∃ d : Label n, (∀ v : Label n, symp d v = Q v + Q (C.symm v)) ∧
      (∀ d' : Label n, (∀ v : Label n, symp d' v = Q v + Q (C.symm v)) → d' = d) ∧
      (∀ ρ : Op (Qubits n), IsDensity ρ →
        ∀ m : Label n, bellProb (U * ρ * Uᴴ) m = bellProb ρ (C.symm (m + d))) ∧
      (∀ T : Submodule (ZMod 2) (Label n), IsIsotropic T →
        (fun m => C m + d) '' affineFilter T = affineFilter (T.map C.toLinearMap)) := by sorry

end BatchStabilizer.Learning
