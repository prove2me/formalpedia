-- Prove2me | solution 1 for rudelson_coordinate_radius_scale_le_expected_deviation_scale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T03:44:15.635086+00:00
-- url     : https://prove2.me/submissions/cd3f43ae-1421-4037-84e3-a8dfdc166d55

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (Csel : ℝ) :
    0 < Csel →
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  intro hCsel
  refine ⟨Csel * Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ r m μ₀ hn1 hn2 hr hm hμ₀
  unfold tangentSamplingExpectedDeviationScale
  simp only [Nat.cast_max]
  have hn1R : (0 : ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
  have hmaxN : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hmaxR : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hmaxN
  have hmax1 : (1 : ℝ) ≤ (max n₁ n₂ : ℝ) := by
    have : 1 ≤ max n₁ n₂ := hmaxN
    exact_mod_cast this
  have hlognn : 0 ≤ Real.log (max n₁ n₂ : ℝ) := Real.log_nonneg hmax1
  have hμ₀pos : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  -- product n1*n2 ≤ max^2
  have hprod : (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
    have h1 : (n₁ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_left n₁ n₂
    have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_right n₁ n₂
    calc (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (n₂ : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hn2R.le
      _ ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hmaxR.le
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: LHS has division by p = 0; in Lean log/0 = 0, sqrt 0 = 0, so LHS = 0.
    subst hm0
    have hL : Real.log (max (n₁:ℝ) (n₂:ℝ)) / (((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by
      simp
    rw [hL, Real.sqrt_zero, mul_zero, zero_mul]
    positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  -- p = m/(n1 n2) > 0
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  -- LHS = Csel * √(log(max)/p) * √(2μ₀r/max).  Combine the two sqrt factors,
  -- and bring Csel*√2 onto a single sqrt on the RHS.
  -- Strategy: square-free comparison via Real.sqrt monotonicity after writing both sides
  -- as (nonneg coeff) * sqrt (nonneg arg).
  -- LHS = Csel * sqrt (A) * sqrt (B) = Csel * sqrt (A*B)
  set A : ℝ := Real.log (max n₁ n₂ : ℝ) / p with hA
  set B : ℝ := 2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ) with hB
  have hApos : 0 ≤ A := by rw [hA]; exact div_nonneg hlognn hppos.le
  have hBpos : 0 ≤ B := by rw [hB]; positivity
  have hmerge : Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) :=
    (Real.sqrt_mul hApos B).symm
  rw [mul_assoc, hmerge]
  -- RHS = Csel * √2 * √(μ₀ * max * r * log(max) / m)
  set D : ℝ := μ₀ * (max n₁ n₂ : ℝ) * (r : ℝ) * Real.log (max n₁ n₂ : ℝ) / (m : ℝ) with hD
  have hDpos : 0 ≤ D := by
    rw [hD]; apply div_nonneg _ hmR.le; positivity
  -- RHS = Csel * (√2 * √D) = Csel * √(2*D)
  rw [mul_assoc]
  rw [show Real.sqrt 2 * Real.sqrt D = Real.sqrt (2 * D) from
    (Real.sqrt_mul (by norm_num) D).symm]
  -- Now reduce to Csel * √(A*B) ≤ Csel * √(2*D), i.e. √(A*B) ≤ √(2*D), i.e. A*B ≤ 2*D.
  apply mul_le_mul_of_nonneg_left _ hCsel.le
  apply Real.sqrt_le_sqrt
  -- A*B = (log(max)/p) * (2μ₀r/max);  2*D = 2 μ₀ max r log(max) / m
  rw [hA, hB, hD, hp]
  -- A*B = log(max) * (n1 n2 / m) * (2 μ₀ r / max)
  rw [div_div_eq_mul_div, div_mul_div_comm]
  -- goal: log(max) * (2μ₀r) / ( (m/(n1n2)) * max )  ≤ 2 * (μ₀ max r log(max) / m)
  -- multiply through; use that everything nonneg. Reduce by clearing denominators.
  -- goal: log(max) * (n1n2) * (2μ₀r) / (m * max)  ≤ 2 * (μ₀ max r log(max) / m)
  have hLMR : 0 ≤ Real.log (max (n₁:ℝ) (n₂:ℝ)) * μ₀ * (r:ℝ) := by positivity
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  rw [mul_div_assoc']  -- RHS: (2 * (μ₀ max r log(max))) / m
  rw [div_le_div_iff₀ (by positivity) hmR]
  -- log(max)*(n1n2)*(2μ₀r) * m ≤ (2*(μ₀ max r log(max))) * (m * max)
  nlinarith [mul_le_mul_of_nonneg_right hprod (by positivity :
      (0:ℝ) ≤ Real.log (max (n₁:ℝ) (n₂:ℝ)) * μ₀ * (r:ℝ) * (m:ℝ) * 2),
    hlognn, hμ₀pos.le, hrR.le, hmaxR.le, hmR.le, hLMR,
    mul_nonneg hLMR hmaxR.le, mul_nonneg (mul_nonneg hLMR hmaxR.le) hmR.le]
