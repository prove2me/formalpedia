-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_lemma_5_8
-- name    : BatchStabilizer.Learning.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:27.891212+00:00
-- url     : https://prove2.me/theorems/db0d7910-3cc4-4979-9143-8c4e9403190a
-- title:
--   Lemma 5.8 — collision excess identity
-- statement:
--   In the analysis setup with $p_x=\sigma_{x,x}$, let $L\subseteq T$ be any subspace of the target label space and $L_0=CL$. Then
--   $$\Delta(L)=\sum_{x\neq y}p_xp_y\,\mathbf 1\{x+y\in\ker H_{L_0}\}\ge0 .$$
--   Thus $\Delta(L)$ is the weight of pairs of distinct computational labels that the partial checks of $L$ do not distinguish.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - encoding: an optimal stabilizer state |ϕ*⟩ with label space T, a Clifford U with U|ϕ*⟩ = |0ⁿ⟩ inducing C as in (53), σ = UρU† → TargetSetup ρ P U C: P = |ϕ*⟩⟨ϕ*| ∈ Stab_n attains stabFidelity ρ, U unitary with UPU† = |0ⁿ⟩⟨0ⁿ| and U W_u U† = ±W_{Cu} for a linear equivalence C; T = labelSpace P; reason: states are compared as projectors (global phase quotiented); a unitary normalizing the Hermitian Paulis is a Clifford, and C is the action (53)
--   - encoding: x + y ∈ ker H_{L₀} for a check matrix whose rows are the Z-components of a basis of L₀ → z·(x+y) = 0 for the Z-component z of every label of L₀ (partialSyndrome C L (x+y) = 0); reason: a vector is annihilated by a basis of functionals iff it is annihilated by their span
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 21 (PDF p. 22), Lemma 5.8, equation (74)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Target

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

open Classical in
/-- Lemma 5.8, printed p. 21 (PDF p. 22): for every `L ⊆ T`,
`Δ(L) = Σ_{x ≠ y} p_x p_y 1{x + y ∈ ker H_{L₀}} ≥ 0` (74). -/
theorem lemma_5_8 {n : ℕ} (ρ P U : Op (Qubits n)) (C : Label n ≃ₗ[ZMod 2] Label n)
    (h : TargetSetup ρ P U C) (L : Submodule (ZMod 2) (Label n)) (hL : L ≤ labelSpace P) :
    collisionExcess (U * ρ * Uᴴ) C L =
        (∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          if x ≠ y ∧ partialSyndrome C L (x + y) = 0 then
            compProb (U * ρ * Uᴴ) x * compProb (U * ρ * Uᴴ) y else 0) ∧
      0 ≤ collisionExcess (U * ρ * Uᴴ) C L := by sorry

end BatchStabilizer.Learning
