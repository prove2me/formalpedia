-- Prove2me | solution 1 for section5_clean_qht_coefficient_transfer
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:00.445452+00:00
-- url     : https://prove2.me/submissions/96e76315-97c6-4c5b-a574-9d313cd4c4e2

import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_Section5Verified_Section5CleanSubspace
import Definitions.Def_Section5Verified_Section5HermiteTransfer
import Mathlib
import Theorems.Thm_section5_tensor_inverse_coefficient_transfer
section
set_option autoImplicit false

/-!
The operator-norm transfer in the proof of Theorem 5.2, Eqs. (162)--(166).
The synthesis maps have the clean ancilla subspace as their domain; taking
their adjoints therefore gives the projected inverse coefficients.
-/











theorem section5_uniform_synthesis_operator_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A S : E →L[ℂ] F) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ c : E, ‖c‖ = 1 → ‖A c-S c‖ ≤ δ) : ‖A-S‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hδ
  intro c hc
  exact h c hc











































end
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (U : EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ β)
    (S : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η) (hη' : η < 1/2)
    (hsynth : ∀ c : EuclideanSpace ℂ α, ‖c‖ = 1 →
      ‖U (section5_basis_embedding e c)-S c‖ ≤ η/(4*n))
    (ψ : EuclideanSpace ℂ (Fin n → β)) (hψ : ‖ψ‖ ≤ 1)
    (c : EuclideanSpace ℂ (Fin n → α))
    (hdisc : ‖ContinuousLinearMap.adjoint (section5_tensor_power S n) ψ-c‖ ≤ η/2) :
    ‖ContinuousLinearMap.adjoint
        (section5_tensor_power
          (U.toLinearIsometry.toContinuousLinearMap ∘L
            (section5_basis_embedding e).toContinuousLinearMap) n) ψ-c‖ ≤ η := by
  let A := U.toLinearIsometry.toContinuousLinearMap ∘L
    (section5_basis_embedding e).toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖U (section5_basis_embedding e x)‖ ≤ 1*‖x‖
    simp only [U.norm_map, LinearIsometry.norm_map, one_mul, le_refl]
  have hAS : ‖A-S‖ ≤ η/(4*n) :=
    section5_uniform_synthesis_operator_bound A S _ (by positivity) hsynth
  exact section5_tensor_inverse_coefficient_transfer A S n hn η hη hη' hA hAS ψ hψ c hdisc
