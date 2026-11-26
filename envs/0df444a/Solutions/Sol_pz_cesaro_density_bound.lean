-- Prove2me | solution 1 for pz_cesaro_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:13:50.789962+00:00
-- url     : https://prove2.me/submissions/5a129702-22bf-4a6c-baf8-b9a0d82b86ee

import Mathlib

theorem solution :
  ∀ K : Real, 0 ≤ K → ∀ ρ' : Real, 0 < ρ' →
    ∃ M : Real, ∀ Λ A α β d : Real, M ≤ Λ → 0 ≤ A → A ≤ Λ * Real.sqrt Λ →
      Λ - 1 ≤ α → α ≤ K + Real.sqrt (β * (1 - d)) →
      β ≤ Λ^2 + A / 2 + 1 → 0 ≤ d → d ≤ 1 → d ≤ ρ' := by
  intro K hK ρ' hρ'
  have hρ'nn : (0 : ℝ) ≤ ρ' := hρ'.le
  have hρ'ne : ρ' ≠ 0 := ne_of_gt hρ'
  refine ⟨(K + 2) + (3 / (2 * ρ')) ^ 2 + 6 * (K + 1) / ρ' + Real.sqrt (3 / ρ') + 1, ?_⟩
  intro Λ A α β d hMΛ hA0 hA hα1 hα2 hβ hd0 hd1
  -- nonnegativity of the threshold summands
  have hs2 : (0 : ℝ) ≤ (3 / (2 * ρ')) ^ 2 := sq_nonneg _
  have h6nn : (0 : ℝ) ≤ 6 * (K + 1) / ρ' := div_nonneg (by linarith) hρ'nn
  have hsnn : (0 : ℝ) ≤ Real.sqrt (3 / ρ') := Real.sqrt_nonneg _
  have hK2 : (0 : ℝ) ≤ K + 2 := by linarith
  -- Λ dominates each threshold piece
  have hΛK : K + 2 ≤ Λ := le_trans (by linarith) hMΛ
  have hΛ2' : (3 / (2 * ρ')) ^ 2 ≤ Λ := le_trans (by linarith) hMΛ
  have hΛ6 : 6 * (K + 1) / ρ' ≤ Λ := le_trans (by linarith) hMΛ
  have hΛs : Real.sqrt (3 / ρ') ≤ Λ := le_trans (by linarith) hMΛ
  have hΛ : (0 : ℝ) < Λ := by linarith
  -- √Λ ≥ 3 / (2ρ'), hence 2ρ'√Λ ≥ 3
  have hsqrtΛ : 3 / (2 * ρ') ≤ Real.sqrt Λ := by
    rw [Real.le_sqrt' (show (0 : ℝ) < 3 / (2 * ρ') by positivity)]
    exact hΛ2'
  have h3 : (3 : ℝ) ≤ 2 * ρ' * Real.sqrt Λ := by
    have h := mul_le_mul_of_nonneg_left hsqrtΛ (show (0 : ℝ) ≤ 2 * ρ' by linarith)
    have e : 2 * ρ' * (3 / (2 * ρ')) = 3 := by field_simp
    linarith
  -- ρ' Λ ≥ 6 (K + 1)
  have h6K : 6 * (K + 1) ≤ ρ' * Λ := by
    have h := mul_le_mul_of_nonneg_left hΛ6 hρ'nn
    have e : ρ' * (6 * (K + 1) / ρ') = 6 * (K + 1) := by field_simp
    linarith
  -- Λ² ≥ 3 / ρ'
  have hΛsq : 3 / ρ' ≤ Λ ^ 2 := by
    have hnn : (0 : ℝ) ≤ 3 / ρ' := div_nonneg (by norm_num) hρ'nn
    have hprod : (0 : ℝ) ≤ (Λ - Real.sqrt (3 / ρ')) * (Λ + Real.sqrt (3 / ρ')) :=
      mul_nonneg (sub_nonneg.mpr hΛs) (add_nonneg hΛ.le (Real.sqrt_nonneg _))
    have hss : (Real.sqrt (3 / ρ')) ^ 2 = 3 / ρ' := Real.sq_sqrt hnn
    nlinarith [hprod, hss]
  -- the three pieces of the numerator bound, each ≤ ρ' Λ² / 3
  have hQ1 : Λ * Real.sqrt Λ / 2 ≤ ρ' * Λ ^ 2 / 3 := by
    have hprod : (0 : ℝ) ≤ Λ * Real.sqrt Λ * (2 * ρ' * Real.sqrt Λ - 3) :=
      mul_nonneg (mul_nonneg hΛ.le (Real.sqrt_nonneg _)) (by linarith [h3])
    have hss : (Real.sqrt Λ) ^ 2 = Λ := Real.sq_sqrt hΛ.le
    nlinarith [hprod, hss]
  have hQ2 : 2 * (K + 1) * Λ ≤ ρ' * Λ ^ 2 / 3 := by
    have hprod : (0 : ℝ) ≤ Λ * (ρ' * Λ - 6 * (K + 1)) :=
      mul_nonneg hΛ.le (by linarith [h6K])
    nlinarith [hprod]
  have hQ3 : (1 : ℝ) ≤ ρ' * Λ ^ 2 / 3 := by
    have h := mul_le_mul_of_nonneg_left hΛsq hρ'nn
    have e : ρ' * (3 / ρ') = 3 := by field_simp
    linarith
  -- main chain: (Λ - 1 - K) ≤ √(β (1 - d)), square it
  have hα : Λ - 1 - K ≤ Real.sqrt (β * (1 - d)) := by linarith
  have h1 : (0 : ℝ) < Λ - 1 - K := by linarith
  have hβpos : (0 : ℝ) ≤ β * (1 - d) := by
    by_contra hcon
    push_neg at hcon
    have hz : Real.sqrt (β * (1 - d)) = 0 := Real.sqrt_eq_zero_of_nonpos hcon.le
    linarith
  have hsq : (Λ - 1 - K) ^ 2 ≤ β * (1 - d) := by
    have hprod : (0 : ℝ) ≤ (Real.sqrt (β * (1 - d)) - (Λ - 1 - K)) *
        (Real.sqrt (β * (1 - d)) + (Λ - 1 - K)) :=
      mul_nonneg (sub_nonneg.mpr hα) (add_nonneg (Real.sqrt_nonneg _) h1.le)
    have hss : (Real.sqrt (β * (1 - d))) ^ 2 = β * (1 - d) := Real.sq_sqrt hβpos
    nlinarith [hprod, hss]
  -- set B := Λ² + Λ√Λ / 2 + 1 and push β (1 - d) ≤ B (1 - d)
  set B : ℝ := Λ ^ 2 + Λ * Real.sqrt Λ / 2 + 1 with hBdef
  have hBpos : (0 : ℝ) < B := by
    have g1 : (0 : ℝ) ≤ Λ ^ 2 := sq_nonneg Λ
    have g2 : (0 : ℝ) ≤ Λ * Real.sqrt Λ / 2 :=
      div_nonneg (mul_nonneg hΛ.le (Real.sqrt_nonneg _)) (by norm_num)
    rw [hBdef]
    linarith
  have hstep : β * (1 - d) ≤ B * (1 - d) := by
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hd1)
    have hA2 : A / 2 ≤ Λ * Real.sqrt Λ / 2 := by linarith
    rw [hBdef]
    linarith
  have h1d : (Λ - 1 - K) ^ 2 / B ≤ 1 - d := by
    rw [div_le_iff₀ hBpos]
    calc (Λ - 1 - K) ^ 2 ≤ β * (1 - d) := hsq
    _ ≤ B * (1 - d) := hstep
    _ = (1 - d) * B := by ring
  have hdle : d ≤ (B - (Λ - 1 - K) ^ 2) / B := by
    have e : (B - (Λ - 1 - K) ^ 2) / B = 1 - (Λ - 1 - K) ^ 2 / B := by
      rw [sub_div, div_self (ne_of_gt hBpos)]
    rw [e]
    linarith
  have hnum : B - (Λ - 1 - K) ^ 2 ≤ ρ' * B := by
    have hexpand : B - (Λ - 1 - K) ^ 2
        = Λ * Real.sqrt Λ / 2 + 2 * (K + 1) * Λ + 1 - (K + 1) ^ 2 := by
      rw [hBdef]
      ring
    have hBge : Λ ^ 2 ≤ B := by
      have g2 : (0 : ℝ) ≤ Λ * Real.sqrt Λ / 2 :=
        div_nonneg (mul_nonneg hΛ.le (Real.sqrt_nonneg _)) (by norm_num)
      rw [hBdef]
      linarith
    have hsum : Λ * Real.sqrt Λ / 2 + 2 * (K + 1) * Λ + 1 ≤ ρ' * Λ ^ 2 := by
      linarith [hQ1, hQ2, hQ3]
    have hρB : ρ' * Λ ^ 2 ≤ ρ' * B := mul_le_mul_of_nonneg_left hBge hρ'nn
    have hsqK : (0 : ℝ) ≤ (K + 1) ^ 2 := sq_nonneg _
    rw [hexpand]
    linarith
  calc d ≤ (B - (Λ - 1 - K) ^ 2) / B := hdle
  _ ≤ ρ' := by
    rw [div_le_iff₀ hBpos]
    exact hnum
