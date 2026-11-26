-- Prove2me | solution 1 for section5_projDist_inverse_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:32.566496+00:00
-- url     : https://prove2.me/submissions/21ac28f6-7d0c-471f-b602-4aae3d9caf5a

import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_Section5Verified_Section5CleanSubspace
import Mathlib
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Basis encodings and clean ancillary workspace in Theorem 5.2. -/



theorem section5_basis_embedding_basis {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (a : α) :
    section5_basis_embedding e (EuclideanSpace.basisFun α ℂ a) =
      EuclideanSpace.basisFun β ℂ (e a) := by
  classical
  change ((EuclideanSpace.basisFun α ℂ).toBasis.constr ℂ
      (fun i => EuclideanSpace.basisFun β ℂ (e i)))
    ((EuclideanSpace.basisFun α ℂ).toBasis a) = _
  exact Module.Basis.constr_basis (EuclideanSpace.basisFun α ℂ).toBasis ℂ _ a

theorem section5_basis_embedding_adjoint {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (ψ : EuclideanSpace ℂ β) (a : α) :
    ContinuousLinearMap.adjoint (section5_basis_embedding e).toContinuousLinearMap ψ a = ψ (e a) := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (section5_basis_embedding e).toContinuousLinearMap (EuclideanSpace.basisFun α ℂ a) ψ
  simpa only [EuclideanSpace.basisFun_inner, LinearIsometry.coe_toContinuousLinearMap,
    section5_basis_embedding_basis] using h











theorem section5_projDist_clean_coefficients (n q a D : ℕ) (hD : D ≤ 2^q)
    (w : EuclideanSpace ℝ (Fin n)) (F : EuclideanSpace ℂ (Qubits (n*q+a))) :
    projDist n q a D w F =
      ‖ContinuousLinearMap.adjoint
          (section5_basis_embedding (section5_clean_degree_encoding n q a D hD)).toContinuousLinearMap F-
        section5_ideal_hermite_coefficients n D w‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold projDist
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  rw [PiLp.sub_apply, section5_basis_embedding_adjoint]
  rfl



end
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution (n q a D : ℕ) (hD : D ≤ 2^q)
    (w : EuclideanSpace ℝ (Fin n))
    (U : EuclideanSpace ℂ (Qubits (n*q+a)) →L[ℂ] EuclideanSpace ℂ (Qubits (n*q+a)))
    (ψ : EuclideanSpace ℂ (Qubits (n*q+a))) :
    projDist n q a D w (ContinuousLinearMap.adjoint U ψ) =
      ‖ContinuousLinearMap.adjoint
          (U ∘L (section5_basis_embedding (section5_clean_degree_encoding n q a D hD)).toContinuousLinearMap) ψ-
        section5_ideal_hermite_coefficients n D w‖ := by
  rw [section5_projDist_clean_coefficients n q a D hD w (ContinuousLinearMap.adjoint U ψ)]
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
