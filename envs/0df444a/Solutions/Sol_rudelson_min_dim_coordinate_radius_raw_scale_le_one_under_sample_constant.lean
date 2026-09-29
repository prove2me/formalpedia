-- Prove2me | solution 1 for rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T03:19:48.957716+00:00
-- url     : https://prove2.me/submissions/61c4ed96-0591-4b89-8b19-1c6a466053d0

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

private lemma max_mul_min_cast_div
    {n₁ n₂ : ℕ} (hmin : 0 < min n₁ n₂) :
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ) =
      ((max n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
    max_mul_min n₁ n₂
  have hprod :
      ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) =
        (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hprod_nat
  have hmin_ne : ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hmin)
  calc
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ)
        = (((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ)) /
            ((min n₁ n₂ : ℕ) : ℝ) := by rw [hprod]
    _ = ((max n₁ n₂ : ℕ) : ℝ) := by field_simp [hmin_ne]

theorem solution
    (Ccoord : ℝ) :
    0 < Ccoord →
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        Real.sqrt
            (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤ 1 := by
  intro hCcoord
  refine ⟨max 1 Ccoord, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m μ₀ hn₁ hn₂ hr _hm hμ₀ hmLower
  let C : ℝ := max 1 Ccoord
  let N : ℝ := (max n₁ n₂ : ℕ)
  let mn : ℝ := (min n₁ n₂ : ℕ)
  let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
  let L : ℝ := Real.log N
  let A : ℝ :=
    Real.sqrt
        (Real.log (↑(max n₁ n₂)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      Real.sqrt
        (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
  have hCcoord_le_C' : Ccoord ≤ C' := by
    exact le_trans (le_max_right (1 : ℝ) Ccoord) hC'
  have hC'_nonneg : 0 ≤ C' := by
    exact le_trans (le_trans zero_le_one (le_max_left (1 : ℝ) Ccoord)) hC'
  have hmin_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hN_nat
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hN_one
  have hmn_pos : 0 < mn := by
    dsimp [mn]
    exact_mod_cast hmin_nat
  have hnn_pos : 0 < nn := by
    dsimp [nn]
    positivity
  have hμ_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hβ_ge_one : (1 : ℝ) ≤ β := by linarith
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  by_cases hmzero : m = 0
  · subst m
    simp
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hmzero
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
    have hnn_div_min : nn / mn = N := by
      simpa [nn, mn, N] using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
    have hK_nonneg : 0 ≤ μ₀ * N * (r : ℝ) * L := by
      dsimp [N, L]
      positivity
    have hK_le_betaK :
        μ₀ * N * (r : ℝ) * L ≤ β * (μ₀ * N * (r : ℝ) * L) := by
      calc
        μ₀ * N * (r : ℝ) * L
            = (1 : ℝ) * (μ₀ * N * (r : ℝ) * L) := by ring
        _ ≤ β * (μ₀ * N * (r : ℝ) * L) :=
            mul_le_mul_of_nonneg_right hβ_ge_one hK_nonneg
    have hcoordK_le :
        Ccoord * (μ₀ * N * (r : ℝ) * L) ≤
          C' * (β * (μ₀ * N * (r : ℝ) * L)) := by
      exact le_trans
        (mul_le_mul_of_nonneg_right hCcoord_le_C' hK_nonneg)
        (mul_le_mul_of_nonneg_left hK_le_betaK hC'_nonneg)
    have hnum_le_m :
        Ccoord * μ₀ * N * (r : ℝ) * L ≤ (m : ℝ) := by
      have hmLower' :
          (m : ℝ) ≥ C' * μ₀ * N * (r : ℝ) * (β * L) := by
        simpa [N, L, mul_assoc] using hmLower
      have hshape :
          Ccoord * μ₀ * N * (r : ℝ) * L =
            Ccoord * (μ₀ * N * (r : ℝ) * L) := by ring
      have htarget :
          C' * (β * (μ₀ * N * (r : ℝ) * L)) =
            C' * μ₀ * N * (r : ℝ) * (β * L) := by ring
      calc
        Ccoord * μ₀ * N * (r : ℝ) * L
            = Ccoord * (μ₀ * N * (r : ℝ) * L) := hshape
        _ ≤ C' * (β * (μ₀ * N * (r : ℝ) * L)) := hcoordK_le
        _ = C' * μ₀ * N * (r : ℝ) * (β * L) := htarget
        _ ≤ (m : ℝ) := hmLower'
    have hratio_le_one :
        (Ccoord * μ₀ * N * (r : ℝ) * L) / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hm_pos]
      simpa using hnum_le_m
    have harg1_nonneg :
        0 ≤ Real.log (↑(max n₁ n₂)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
      positivity
    have harg2_nonneg :
        0 ≤ Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
      positivity
    have hproduct_eq :
        (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) =
          (Ccoord * μ₀ * N * (r : ℝ) * L) / (m : ℝ) := by
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      have hmn_ne : mn ≠ 0 := ne_of_gt hmn_pos
      have hnn_ne : nn ≠ 0 := ne_of_gt hnn_pos
      field_simp [N, mn, nn, L, hm_ne, hmn_ne, hnn_ne]
      have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
        max_mul_min n₁ n₂
      have hprod :
          (n₁ : ℝ) * (n₂ : ℝ) = N * mn := by
        have hprod' : N * mn = (n₁ : ℝ) * (n₂ : ℝ) := by
          dsimp [N, mn]
          exact_mod_cast hprod_nat
        exact hprod'.symm
      calc
        Real.log (↑(max n₁ n₂)) * (n₁ : ℝ) * (n₂ : ℝ)
            = L * ((n₁ : ℝ) * (n₂ : ℝ)) := by
              dsimp [L]
              ring
        _ = L * (N * mn) := by rw [hprod]
        _ = mn * N * L := by ring
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    have hA_sq :
        A ^ 2 =
          (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
      dsimp [A]
      rw [mul_pow, Real.sq_sqrt harg1_nonneg, Real.sq_sqrt harg2_nonneg]
    have hA_sq_le_one : A ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [hA_sq, hproduct_eq]
      simpa using hratio_le_one
    have hA_le_one : A ≤ 1 :=
      (sq_le_sq₀ hA_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ))).mp hA_sq_le_one
    simpa [A] using hA_le_one
