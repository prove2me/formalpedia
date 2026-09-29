-- Prove2me | solution 1 for mme_CW_q6_coupled_rounding_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:03:56.714615+00:00
-- url     : https://prove2.me/submissions/ca85c252-8532-4710-9a04-0410f8507a91

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_CW_coupled_pruning_ratio

open MME Filter

namespace CWQ6CoupledRoundingPackage

noncomputable def lambda (tau : ℝ) : ℝ :=
  2 / ((6 : ℝ) ^ (3 * tau) + 2)

noncomputable def L (tau : ℝ) (N : ℕ) : ℕ :=
  ⌊lambda tau * (N : ℝ)⌋₊

noncomputable def G (tau : ℝ) (N : ℕ) : ℕ :=
  N - L tau N

private lemma lambda_pos (tau : ℝ) : 0 < lambda tau := by
  unfold lambda
  positivity

private lemma lambda_le_one (tau : ℝ) : lambda tau ≤ 1 := by
  unfold lambda
  have hpow : 0 ≤ (6 : ℝ) ^ (3 * tau) := by positivity
  rw [div_le_one (by positivity : (0 : ℝ) < (6 : ℝ) ^ (3 * tau) + 2)]
  linarith

private lemma L_le (tau : ℝ) (N : ℕ) : L tau N ≤ N := by
  unfold L
  apply Nat.floor_le_of_le
  calc
    lambda tau * (N : ℝ) ≤ 1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (lambda_le_one tau) (by positivity)
    _ = (N : ℝ) := one_mul _

private lemma L_add_G (tau : ℝ) (N : ℕ) : L tau N + G tau N = N := by
  unfold G
  exact Nat.add_sub_of_le (L_le tau N)

private lemma tendsto_L_div (tau : ℝ) :
    Tendsto (fun N : ℕ => (L tau N : ℝ) / (N : ℝ)) atTop
      (nhds (lambda tau)) := by
  have hreal :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) (le_of_lt (lambda_pos tau)))
  simpa only [L, Function.comp_def] using hreal.comp tendsto_natCast_atTop_atTop

private lemma tendsto_G_div (tau : ℝ) :
    Tendsto (fun N : ℕ => (G tau N : ℝ) / (N : ℝ)) atTop
      (nhds (1 - lambda tau)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub (tendsto_L_div tau)
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hLN : L tau N ≤ N := L_le tau N
  rw [G, Nat.cast_sub hLN, sub_div,
    div_self (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)]

private lemma limit_pruning_margin_pos
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    0 < 100 * (1 - lambda tau) - 341 * lambda tau := by
  have hQ : (341 : ℝ) / 100 < (6 : ℝ) ^ (3 * tau) / 2 :=
    mme_CW_coupled_pruning_ratio 6 (by norm_num) tau htau
  have hden : 0 < (6 : ℝ) ^ (3 * tau) + 2 := by positivity
  unfold lambda
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

private lemma eventually_pruning_cross_mul
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop, 341 * L tau N < 100 * G tau N := by
  have htend : Tendsto
      (fun N : ℕ =>
        100 * ((G tau N : ℝ) / (N : ℝ)) -
          341 * ((L tau N : ℝ) / (N : ℝ)))
      atTop (nhds (100 * (1 - lambda tau) - 341 * lambda tau)) :=
    (tendsto_const_nhds.mul (tendsto_G_div tau)).sub
      (tendsto_const_nhds.mul (tendsto_L_div tau))
  have hpos : 0 < 100 * (1 - lambda tau) - 341 * lambda tau :=
    limit_pruning_margin_pos tau htau
  have hevent : ∀ᶠ N : ℕ in atTop,
      0 < 100 * ((G tau N : ℝ) / (N : ℝ)) -
        341 * ((L tau N : ℝ) / (N : ℝ)) :=
    (tendsto_order.1 htend).1 0 hpos
  filter_upwards [hevent, eventually_gt_atTop 0] with N hmargin hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hreal : (341 : ℝ) * L tau N < 100 * G tau N := by
    rw [div_eq_mul_inv, div_eq_mul_inv] at hmargin
    nlinarith [inv_pos.mpr hNreal]
  exact_mod_cast hreal

private lemma eventually_L_pos (tau : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < L tau N := by
  exact (tendsto_nat_floor_mul_atTop (lambda tau) (lambda_pos tau)).eventually
    (eventually_gt_atTop 0)

end CWQ6CoupledRoundingPackage

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ L G : ℕ → ℕ,
      (∀ N, L N + G N = N) ∧
      Tendsto (fun N : ℕ => (L N : ℝ) / (N : ℝ)) atTop
        (nhds (2 / ((6 : ℝ) ^ (3 * tau) + 2))) ∧
      Tendsto (fun N : ℕ => (G N : ℝ) / (N : ℝ)) atTop
        (nhds ((6 : ℝ) ^ (3 * tau) /
          ((6 : ℝ) ^ (3 * tau) + 2))) ∧
      ∀ᶠ N : ℕ in atTop,
        0 < L N ∧ 341 * L N < 100 * G N := by
  refine ⟨CWQ6CoupledRoundingPackage.L tau,
    CWQ6CoupledRoundingPackage.G tau, ?_⟩
  refine ⟨CWQ6CoupledRoundingPackage.L_add_G tau, ?_, ?_, ?_⟩
  · simpa only [CWQ6CoupledRoundingPackage.lambda] using
      CWQ6CoupledRoundingPackage.tendsto_L_div tau
  · convert CWQ6CoupledRoundingPackage.tendsto_G_div tau using 1
    unfold CWQ6CoupledRoundingPackage.lambda
    have hden : (6 : ℝ) ^ (3 * tau) + 2 ≠ 0 := by positivity
    field_simp [hden]
    ring_nf
  · filter_upwards
      [CWQ6CoupledRoundingPackage.eventually_L_pos tau,
       CWQ6CoupledRoundingPackage.eventually_pruning_cross_mul tau htau]
      with N hL hratio
    exact ⟨hL, hratio⟩
