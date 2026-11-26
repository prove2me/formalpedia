-- Prove2me | solution 1 for section5_max_column_recovery
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:21.617422+00:00
-- url     : https://prove2.me/submissions/80099654-3abd-404d-9d44-66510f09b505

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_column_norm_bound
import Theorems.Thm_section5_normalize_perturbation
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Reconstruction by an explicitly selected column of an operator. This is the
finite arithmetic step used after powering an accurate rank-one estimate. -/



theorem section5_coordinate_ket_norm {n : ℕ} (i : Fin n) :
    ‖section5_coordinate_ket i‖=1 := by simp [section5_coordinate_ket]







end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (j : Fin n) (hmax : ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 ≤ ρ) (hsmall : 4*n*ρ ≤ α)
    (herror : ‖A-(α:ℂ) • rankOne ℂ v v‖ ≤ ρ) :
    A (section5_coordinate_ket j) ≠ 0 ∧
      ∃ ζ : ℂ, ‖ζ‖=1 ∧
        ‖NormedSpace.normalize (A (section5_coordinate_ket j))-ζ • v‖ ≤ 4*n*ρ/α := by
  let y := A (section5_coordinate_ket j)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hαv : ((α:ℂ) • rankOne ℂ v v) v=(α:ℂ) • v := by
    simp [rankOne_apply,inner_self_eq_norm_sq_to_K,hv]
  have hAv : ‖A v-(α:ℂ) • v‖ ≤ ρ := by
    have hh := (A-(α:ℂ) • rankOne ℂ v v).le_opNorm v
    have he : (A-(α:ℂ) • rankOne ℂ v v) v=A v-(α:ℂ) • v := by
      rw [sub_apply,hαv]
    rw [he,hv,mul_one] at hh
    exact hh.trans herror
  have hnormα : ‖(α:ℂ) • v‖=α := by simp [norm_smul,hv,Complex.norm_real,abs_of_pos hα]
  have hylo : α-ρ ≤ n*‖y‖ := by
    have hh := norm_sub_norm_le ((α:ℂ) • v) (A v)
    rw [hnormα,norm_sub_rev] at hh
    have hc := section5_column_norm_bound A j hmax v hv
    change ‖A v‖ ≤ n*‖y‖ at hc
    linarith
  have hybig : α ≤ 2*n*‖y‖ := by
    have hr : ρ ≤ α/4 := by nlinarith
    linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h,norm_zero,mul_zero] at hybig
    linarith
  let c : ℂ := (α:ℂ)*inner ℂ v (section5_coordinate_ket j)
  have hcerror : ‖y-c • v‖ ≤ ρ := by
    have hh := (A-(α:ℂ) • rankOne ℂ v v).le_opNorm (section5_coordinate_ket j)
    rw [section5_coordinate_ket_norm,mul_one] at hh
    have he : (A-(α:ℂ) • rankOne ℂ v v) (section5_coordinate_ket j)=y-c • v := by
      simp only [sub_apply,smul_apply,rankOne_apply,smul_smul,c,y]
    rw [he] at hh
    exact hh.trans herror
  have hc0 : c ≠ 0 := by
    intro h
    rw [h,zero_smul,sub_zero] at hcerror
    have hyρ : ‖y‖ ≤ ρ := hcerror
    have hh : 2*n*‖y‖ ≤ 2*n*ρ := mul_le_mul_of_nonneg_left hyρ (by positivity)
    nlinarith
  let ζ : ℂ := ‖c‖⁻¹ • c
  have hζ : ‖ζ‖=1 := NormedSpace.norm_normalize hc0
  have hcunit : NormedSpace.normalize (c • v)=ζ • v := by
    unfold NormedSpace.normalize
    rw [norm_smul,hv,mul_one]
    exact (smul_assoc _ _ _).symm
  have hh := section5_normalize_perturbation (c • v) y (smul_ne_zero hc0 (by
    intro h; rw [h,norm_zero] at hv; norm_num at hv)) hy0
  rw [hcunit,norm_sub_rev (c • v) y,
    norm_sub_rev (ζ • v) (NormedSpace.normalize y)] at hh
  refine ⟨hy0,ζ,hζ,hh.trans ?_⟩
  apply (div_le_iff₀ (norm_pos_iff.mpr hy0)).mpr
  have hbound : 2*ρ ≤ (4*n*ρ/α)*‖y‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hα).mpr
    nlinarith [mul_le_mul_of_nonneg_right hybig hρ]
  exact (mul_le_mul_of_nonneg_left hcerror (by norm_num)).trans hbound
