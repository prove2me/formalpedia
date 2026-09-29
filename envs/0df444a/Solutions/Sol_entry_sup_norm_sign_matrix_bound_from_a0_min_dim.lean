-- Prove2me | solution 1 for entry_sup_norm_sign_matrix_bound_from_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T16:19:40.497858+00:00
-- url     : https://prove2.me/submissions/ddd0392b-970d-4b71-b9d4-2b780b38b969

import Mathlib.Data.Fintype.Order
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion
open scoped Classical BigOperators

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma coherence_coordinate_energy_le
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} :
    coherence N r u ≤ μ →
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro hcoh i
  have hscale_pos : 0 < (N : ℝ) / (r : ℝ) :=
    div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hr)
  have hleSup :
      (∑ k : Fin r, (u k i) ^ 2) ≤
        ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 :=
    Finite.le_ciSup (f := fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hsup :
      (⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2) ≤
        μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hscale_pos]
    simpa [coherence, mul_comm, mul_left_comm, mul_assoc] using hcoh
  calc
    (∑ k : Fin r, (u k i) ^ 2)
        ≤ μ / ((N : ℝ) / (r : ℝ)) := le_trans hleSup hsup
    _ = μ * (r : ℝ) / (N : ℝ) := by
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      field_simp [hN', hr']

private lemma min_dim_scale_nonneg
    {n₁ n₂ r : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) {μ₀ : ℝ} (hμ₀ : 1 ≤ μ₀) :
    0 ≤ μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
  positivity

private lemma sqrt_product_rectangular_le_min_scale
    {n₁ n₂ r : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) {μ₀ : ℝ} (hμ₀ : 1 ≤ μ₀) :
    Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) ≤
      μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
  have hA_nonneg : 0 ≤ μ₀ * (r : ℝ) := by positivity
  have hmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hmin_pos : 0 < (((min n₁ n₂ : ℕ) : ℝ)) := Nat.cast_pos.mpr hmin_pos_nat
  have hmin_le₁ : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
    exact_mod_cast min_le_left n₁ n₂
  have hmin_le₂ : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
    exact_mod_cast min_le_right n₁ n₂
  have hfrac₁ :
      μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
        μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
    gcongr
  have hfrac₂ :
      μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
        μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
    gcongr
  have hprod :
      Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) ≤
        Real.sqrt (μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))) := by
    exact mul_le_mul (Real.sqrt_le_sqrt hfrac₁) (Real.sqrt_le_sqrt hfrac₂)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
        Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))
        ≤ Real.sqrt (μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))) := hprod
    _ = μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      rw [← sq]
      exact Real.sq_sqrt (min_dim_scale_nonneg hn₁ hn₂ hr hμ₀)

private lemma sign_matrix_entry_abs_le_from_a0
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    {μ₀ : ℝ} (hμ₀ : 1 ≤ μ₀) (S : SVD M r) :
    A0 S μ₀ →
    ∀ i j,
      |signMatrix S i j| ≤ μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
  intro hA0 i j
  have hu :=
    coherence_coordinate_energy_le hn₁ hr S.u hA0.1 i
  have hv :=
    coherence_coordinate_energy_le hn₂ hr S.v hA0.2 j
  calc
    |signMatrix S i j|
        = |∑ k : Fin r, S.u k i * S.v k j| := by
          simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec]
    _ ≤ ∑ k : Fin r, |S.u k i * S.v k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin r, |S.u k i| * |S.v k j| := by
        simp [abs_mul]
    _ ≤ Real.sqrt (∑ k : Fin r, |S.u k i| ^ 2) *
          Real.sqrt (∑ k : Fin r, |S.v k j| ^ 2) := by
        simpa using
          (Real.sum_mul_le_sqrt_mul_sqrt
            (Finset.univ : Finset (Fin r))
            (fun k => |S.u k i|) (fun k => |S.v k j|))
    _ = Real.sqrt (∑ k : Fin r, (S.u k i) ^ 2) *
          Real.sqrt (∑ k : Fin r, (S.v k j) ^ 2) := by
        simp [sq_abs]
    _ ≤ Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
        exact mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) :=
        sqrt_product_rectangular_le_min_scale hn₁ hn₂ hr hμ₀

/-- A0 incoherence bounds every sign-matrix entry by the rectangular
`μ₀ r / min(n₁,n₂)` scale, hence also bounds the entry-sup norm. -/
theorem solution :
    ∃ Csign : ℝ, 0 < Csign ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (signMatrix S) ≤
          Csign * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨1, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  calc
    entrySupNorm (signMatrix S)
        ≤ μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) :=
        entrySupNorm_le_of_forall_abs_le hn₁ hn₂ (signMatrix S)
          (μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)))
          (sign_matrix_entry_abs_le_from_a0 hn₁ hn₂ hr hμ₀ S hA0)
    _ = (1 : ℝ) * μ₀ * ((r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))) := by
      ring
