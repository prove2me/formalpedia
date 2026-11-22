-- Prove2me | solution 27 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:49.625386+00:00
-- url     : https://prove2.me/submissions/5e8235df-af06-4e0c-a540-2321115fa69b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_BroughanRH_chebyshev
import Theorems.Thm_LandauCriterion_psi_oscillation_of_not_riemannHypothesis

theorem solution : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨C, hbound⟩ := BroughanRH.chebyshev
  obtain ⟨β, c, hβ, hc, hosc⟩ := LandauCriterion.psi_oscillation_of_not_riemannHypothesis hRH
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (β - 1 / 2) / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hexp : β - δ = 1 / 2 + δ := by rw [hδdef]; ring
  have hfreq := (hosc δ hδ).1
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      C * Real.sqrt x * (Real.log x) ^ 2 < c * x ^ (β - δ) := by
    rcases le_or_gt C 0 with hC | hC
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx1
      have hx0 : 0 < x := by linarith
      have h1 : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
      have h2 : 0 < c * x ^ (β - δ) := mul_pos hc (Real.rpow_pos_of_pos hx0 _)
      nlinarith [mul_nonneg (neg_nonneg.mpr hC) h1]
    · have hlo := isLittleO_log_rpow_rpow_atTop (s := δ) 2 hδ
      have hk : 0 < c / (2 * C) := by positivity
      filter_upwards [hlo.def hk, Filter.eventually_ge_atTop (1 : ℝ)] with x hkx hx1
      have hx0 : 0 < x := by linarith
      have hxd : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have e1 : ‖Real.log x ^ (2 : ℝ)‖ = Real.log x ^ 2 := by
        have h2 : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
          simpa using Real.rpow_natCast (Real.log x) 2
        rw [h2, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have e2 : ‖x ^ δ‖ = x ^ δ := by rw [Real.norm_eq_abs, abs_of_pos hxd]
      have e3 : x ^ (β - δ) = Real.sqrt x * x ^ δ := by
        rw [hexp, Real.rpow_add hx0, Real.sqrt_eq_rpow]
      rw [e1, e2] at hkx
      rw [e3]
      have hprod : 0 < Real.sqrt x * x ^ δ := mul_pos hs hxd
      have step1 : C * Real.sqrt x * Real.log x ^ 2 ≤ C * Real.sqrt x * (c / (2 * C) * x ^ δ) :=
        mul_le_mul_of_nonneg_left hkx (by positivity)
      have step2 : C * Real.sqrt x * (c / (2 * C) * x ^ δ) = c / 2 * (Real.sqrt x * x ^ δ) := by
        field_simp
      rw [step2] at step1
      nlinarith
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    (hfreq.and_eventually (hev.and (Filter.eventually_ge_atTop (2 : ℝ)))).exists
  have h1 := hbound x hx3
  have h2 : Chebyshev.psi x - x ≤ |Chebyshev.psi x - x| := le_abs_self _
  linarith
