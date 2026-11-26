-- Prove2me | solution 1 for section5_tensor_inverse_coefficient_transfer
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:29.824882+00:00
-- url     : https://prove2.me/submissions/a95b91f7-79e7-40ac-8a6b-a6cd7f66de7f

import Definitions.Def_Section5Verified_Section5HermiteTransfer
import Mathlib
section
set_option autoImplicit false

/-!
The operator-norm transfer in the proof of Theorem 5.2, Eqs. (162)--(166).
The synthesis maps have the clean ancilla subspace as their domain; taking
their adjoints therefore gives the projected inverse coefficients.
-/







theorem section5_hermite_hybrid_budget (n : ℕ) (hn : 1 ≤ n)
    (η : ℝ) (hη : 0 < η) (hη' : η < 1/2) :
    (1+η/(4*n))^n-1 ≤ η/2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 ≤ η/(4*n) := by positivity
  have hb : 1+η/(4*n) ≤ Real.exp (η/(4*n)) := by
    simpa [add_comm] using Real.add_one_le_exp (η/(4*n))
  have hp : (1+η/(4*n))^n ≤ Real.exp (η/4) := by
    calc
      _ ≤ (Real.exp (η/(4*n)))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = Real.exp ((n:ℝ)*(η/(4*n))) := (Real.exp_nat_mul _ _).symm
      _ = _ := by congr 1; field_simp
  have he := Real.abs_exp_sub_one_le (x := η/4)
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  have he' : Real.exp (η/4)-1 ≤ η/2 := by
    have hl := (le_abs_self (Real.exp (η/4)-1)).trans he
    rw [abs_of_nonneg (by positivity)] at hl
    linarith
  linarith

theorem section5_projected_inverse_stability
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A S : E →L[ℂ] F) (δ : ℝ) (hδ : ‖A-S‖ ≤ δ) (ψ : F) :
    ‖ContinuousLinearMap.adjoint A ψ-ContinuousLinearMap.adjoint S ψ‖ ≤ δ*‖ψ‖ := by
  have heq : ContinuousLinearMap.adjoint A ψ-ContinuousLinearMap.adjoint S ψ =
      (ContinuousLinearMap.adjoint (A-S)) ψ := by
    simp
  rw [heq]
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint (A-S)‖*‖ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖A-S‖*‖ψ‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right hδ (norm_nonneg _)



theorem section5_hermite_coefficient_transfer
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A S : E →L[ℂ] F) (ψ : F) (c : E) (η : ℝ)
    (hψ : ‖ψ‖ ≤ 1) (hη : 0 ≤ η) (hAS : ‖A-S‖ ≤ η/2)
    (hdisc : ‖ContinuousLinearMap.adjoint S ψ-c‖ ≤ η/2) :
    ‖ContinuousLinearMap.adjoint A ψ-c‖ ≤ η := by
  have hi := section5_projected_inverse_stability A S (η/2) hAS ψ
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint A ψ-ContinuousLinearMap.adjoint S ψ‖+
        ‖ContinuousLinearMap.adjoint S ψ-c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η/2*1+η/2 := add_le_add
      (hi.trans (mul_le_mul_of_nonneg_left hψ (by positivity))) hdisc
    _ = _ := by ring



theorem section5_isometry_transport_norm
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    (e : E ≃ₗᵢ[ℂ] E') (f : F ≃ₗᵢ[ℂ] F') (A : E →L[ℂ] F) :
    ‖section5_isometry_transport e f A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖f (A (e.symm x))‖ ≤ ‖A‖*‖x‖
  rw [f.norm_map]
  simpa only [e.symm.norm_map] using A.le_opNorm (e.symm x)

theorem section5_isometry_transport_sub
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    (e : E ≃ₗᵢ[ℂ] E') (f : F ≃ₗᵢ[ℂ] F') (A B : E →L[ℂ] F) :
    section5_isometry_transport e f (A-B) =
      section5_isometry_transport e f A-section5_isometry_transport e f B := by
  ext x
  simp [section5_isometry_transport]



theorem section5_tensor_matrix_norm
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ δ) :
    ‖section5_tensor_matrix A B‖ ≤ ‖A‖*‖B‖ :=
  (section5_isometry_transport_norm _ _ _).trans (TensorProduct.norm_mapL_le A B)



theorem section5_tensor_matrix_sub_left
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A A' : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ δ) :
    section5_tensor_matrix (A-A') B = section5_tensor_matrix A B-section5_tensor_matrix A' B := by
  have h : TensorProduct.mapL (A-A') B = TensorProduct.mapL A B-TensorProduct.mapL A' B := by
    calc
      _ = TensorProduct.mapL (A+(-1:ℂ) • A') B := by rw [neg_one_smul ℂ A', sub_eq_add_neg]
      _ = TensorProduct.mapL A B+(-1:ℂ) • TensorProduct.mapL A' B := by
        rw [TensorProduct.mapL_add_left, TensorProduct.mapL_smul_left]
      _ = _ := by rw [neg_one_smul ℂ (TensorProduct.mapL A' B), sub_eq_add_neg]
  simp only [section5_tensor_matrix, h, section5_isometry_transport_sub]

theorem section5_tensor_matrix_sub_right
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B B' : EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ δ) :
    section5_tensor_matrix A (B-B') = section5_tensor_matrix A B-section5_tensor_matrix A B' := by
  have h : TensorProduct.mapL A (B-B') = TensorProduct.mapL A B-TensorProduct.mapL A B' := by
    calc
      _ = TensorProduct.mapL A (B+(-1:ℂ) • B') := by rw [neg_one_smul ℂ B', sub_eq_add_neg]
      _ = TensorProduct.mapL A B+(-1:ℂ) • TensorProduct.mapL A B' := by
        rw [TensorProduct.mapL_add_right, TensorProduct.mapL_smul_right]
      _ = _ := by rw [neg_one_smul ℂ (TensorProduct.mapL A B'), sub_eq_add_neg]
  simp only [section5_tensor_matrix, h, section5_isometry_transport_sub]







theorem section5_tensor_cons_norm
    {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ (Fin n → α) →L[ℂ] EuclideanSpace ℂ (Fin n → β)) :
    ‖section5_tensor_cons n A B‖ ≤ ‖A‖*‖B‖ :=
  (section5_isometry_transport_norm _ _ _).trans (section5_tensor_matrix_norm A B)



theorem section5_tensor_cons_sub_left
    {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (A A' : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B : EuclideanSpace ℂ (Fin n → α) →L[ℂ] EuclideanSpace ℂ (Fin n → β)) :
    section5_tensor_cons n (A-A') B = section5_tensor_cons n A B-section5_tensor_cons n A' B := by
  simp only [section5_tensor_cons, section5_tensor_matrix_sub_left, section5_isometry_transport_sub]

theorem section5_tensor_cons_sub_right
    {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (B B' : EuclideanSpace ℂ (Fin n → α) →L[ℂ] EuclideanSpace ℂ (Fin n → β)) :
    section5_tensor_cons n A (B-B') = section5_tensor_cons n A B-section5_tensor_cons n A B' := by
  simp only [section5_tensor_cons, section5_tensor_matrix_sub_right, section5_isometry_transport_sub]



theorem section5_tensor_power_norm {α β : Type*} [Fintype α] [Fintype β]
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β) (n : ℕ) :
    ‖section5_tensor_power A n‖ ≤ ‖A‖^n := by
  induction n with
  | zero =>
    simpa only [section5_tensor_power, pow_zero] using
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (section5_empty_tuple_equiv α β)).toLinearIsometry.norm_toContinuousLinearMap_le
  | succ n ih =>
    exact (section5_tensor_cons_norm n A _).trans
      ((mul_le_mul_of_nonneg_left ih (norm_nonneg A)).trans_eq (by rw [pow_succ]; ring))



theorem section5_tensor_power_hybrid {α β : Type*} [Fintype α] [Fintype β]
    (A S : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (δ : ℝ) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 1) (hAS : ‖A-S‖ ≤ δ) (n : ℕ) :
    ‖section5_tensor_power A n-section5_tensor_power S n‖ ≤ (1+δ)^n-1 := by
  have hS : ‖S‖ ≤ 1+δ := by
    calc
      _ = ‖A-(A-S)‖ := by congr 1; abel
      _ ≤ ‖A‖+‖A-S‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hA hAS
  induction n with
  | zero => simp [section5_tensor_power]
  | succ n ih =>
    have hp : ‖section5_tensor_power A n‖ ≤ 1 :=
      (section5_tensor_power_norm A n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg A) hA n)
    have hid : section5_tensor_power A (n+1)-section5_tensor_power S (n+1) =
        section5_tensor_cons n (A-S) (section5_tensor_power A n) +
        section5_tensor_cons n S (section5_tensor_power A n-section5_tensor_power S n) := by
      rw [section5_tensor_cons_sub_left, section5_tensor_cons_sub_right]
      simp only [section5_tensor_power]
      abel
    rw [hid]
    calc
      _ ≤ ‖section5_tensor_cons n (A-S) (section5_tensor_power A n)‖+
          ‖section5_tensor_cons n S (section5_tensor_power A n-section5_tensor_power S n)‖ :=
        norm_add_le _ _
      _ ≤ ‖A-S‖*‖section5_tensor_power A n‖+
          ‖S‖*‖section5_tensor_power A n-section5_tensor_power S n‖ :=
        add_le_add (section5_tensor_cons_norm _ _ _) (section5_tensor_cons_norm _ _ _)
      _ ≤ δ*1+(1+δ)*((1+δ)^n-1) := add_le_add
        (mul_le_mul hAS hp (norm_nonneg _) hδ)
        (mul_le_mul hS ih (norm_nonneg _) (by positivity))
      _ = (1+δ)^(n+1)-1 := by rw [pow_succ]; ring



end
set_option autoImplicit false
theorem solution
    {α β : Type*} [Fintype α] [Fintype β]
    (A S : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η) (hη' : η < 1/2)
    (hA : ‖A‖ ≤ 1) (hAS : ‖A-S‖ ≤ η/(4*n))
    (ψ : EuclideanSpace ℂ (Fin n → β)) (hψ : ‖ψ‖ ≤ 1)
    (c : EuclideanSpace ℂ (Fin n → α))
    (hdisc : ‖ContinuousLinearMap.adjoint (section5_tensor_power S n) ψ-c‖ ≤ η/2) :
    ‖ContinuousLinearMap.adjoint (section5_tensor_power A n) ψ-c‖ ≤ η := by
  apply section5_hermite_coefficient_transfer _ _ ψ c η hψ hη.le _ hdisc
  exact (section5_tensor_power_hybrid A S (η/(4*n)) (by positivity) hA hAS n).trans
    (section5_hermite_hybrid_budget n hn η hη hη')
