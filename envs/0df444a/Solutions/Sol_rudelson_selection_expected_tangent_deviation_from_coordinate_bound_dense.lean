-- Prove2me | solution 1 for rudelson_selection_expected_tangent_deviation_from_coordinate_bound_dense
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T03:56:14.161437+00:00
-- url     : https://prove2.me/submissions/5606e053-52b2-4b32-806c-e1b4330607ef

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_tangent_coordinate_frobenius_sq_bound_implies_radius_bound
import Theorems.Thm_rudelson_coordinate_radius_scale_le_expected_deviation_scale
import Theorems.Thm_rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

open MatrixCompletion
open scoped Classical BigOperators

/-! Reduction of `rudelson_selection_..._from_coordinate_bound_dense` (43b949c7, the corrected
    `_dense` variant of the false ancestor 8b5f4a2f) to the PROVISO radius node
    `rudelson_selection_..._from_coordinate_radius_bound_dense_proviso` (66bc91bf), which carries
    the CR Thm 4.2 Part 1 desymmetrization proviso `√(log/p)·R ≤ 1`.

    Bridges (all Proved on platform):
      - tangent_coordinate_frobenius_sq_bound_implies_radius_bound (b82377ce).
      - rudelson_coordinate_radius_scale_le_expected_deviation_scale (6f0d8e45).

    KEY: the proviso is SUPPLIED from the density hypothesis. With R=√(2μ₀r/max),
    (√(log/p)·R)² = (log·min·max/m)·(2μ₀r/max) = 2μ₀·min·r·log/m ≤ 2μ₀·max·r·log/m ≤ 2/β < 1.

    Source: Candès–Recht 2009, arXiv:0805.4471, eq (4.8) p.18 + Thm 4.2 Part 1 eq (4.9) p.18
    (radius-form selection estimate WITH the RHS≤1 proviso). -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        TangentCoordinateFrobeniusBound S
          (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  obtain ⟨Csel, hCsel, Hrad⟩ :=
    rudelson_selection_expected_tangent_deviation_from_coordinate_radius_bound_dense_proviso
  obtain ⟨C, hC, Hscale⟩ :=
    rudelson_coordinate_radius_scale_le_expected_deviation_scale Csel hCsel
  refine ⟨C, hC, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hμ₀ hTCB hdens
  have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hn1R : (0 : ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
  have hminN : 0 < min n₁ n₂ := by omega
  have hminR : (0 : ℝ) < (min n₁ n₂ : ℝ) := by exact_mod_cast hminN
  have hmaxN : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hmaxR : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hmaxN
  set radiusSq : ℝ := 2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ) with hRsq
  have hRsqnn : 0 ≤ radiusSq := by rw [hRsq]; positivity
  set R : ℝ := Real.sqrt radiusSq with hR
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hpt : ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R :=
    tangent_coordinate_frobenius_sq_bound_implies_radius_bound S radiusSq hRsqnn hTCB
  have hlognn : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℕ) ≤ max n₁ n₂ := hmaxN
    exact_mod_cast this
  have hβnn : 0 ≤ β := by linarith
  have hmaxRcast : (0 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by positivity
  have hdens_rad : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) *
      Real.log (↑(max n₁ n₂)) := by
    refine le_trans ?_ hdens
    have hbase : 0 ≤ β * (↑(max n₁ n₂) : ℝ) * (r : ℝ) * Real.log (↑(max n₁ n₂)) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hβnn hmaxRcast) hrR) hlognn
      simpa [mul_assoc] using this
    nlinarith [hbase, hμ₀,
      mul_nonneg (mul_nonneg (mul_nonneg hβnn hmaxRcast) hrR) hlognn]
  -- supply proviso √(log/p)·R ≤ 1
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hprov : Real.sqrt (Real.log (↑(max n₁ n₂)) /
          (((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R ≤ 1 := by
      have : Real.log (↑(max n₁ n₂)) / (((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by simp
      rw [this, Real.sqrt_zero, zero_mul]; norm_num
    have hExp := Hrad β hβ n₁ n₂ r 0 M S R hn1 hn2 hr hm hRnn hdens_rad hprov hpt
    refine le_trans hExp ?_
    rw [hR]
    exact Hscale n₁ n₂ r 0 μ₀ hn1 hn2 hr hm hμ₀
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  set A : ℝ := Real.log (↑(max n₁ n₂) : ℝ) / p with hAdef
  have hApos : 0 ≤ A := by rw [hAdef]; exact div_nonneg hlognn hppos.le
  have hprov : Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R ≤ 1 := by
    have hmerge : Real.sqrt A * R = Real.sqrt (A * radiusSq) := by
      rw [hR, ← Real.sqrt_mul hApos]
    have hprodeq : (n₁ : ℝ) * (n₂ : ℝ) = (min n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
      have := congrArg (Nat.cast : ℕ → ℝ) ((min_mul_max n₁ n₂).symm)
      push_cast at this; exact this
    have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
    have hminne : (min n₁ n₂ : ℝ) ≠ 0 := ne_of_gt hminR
    have hmaxne : (max n₁ n₂ : ℝ) ≠ 0 := ne_of_gt hmaxR
    -- A * radiusSq = (log/p)·(2μ₀r/max) = 2μ₀·min·r·log/m
    have hval : A * radiusSq
        = 2 * μ₀ * (↑(min n₁ n₂):ℝ) * (r:ℝ) * Real.log (↑(max n₁ n₂)) / (m:ℝ) := by
      rw [hAdef, hRsq, hp, hprodeq]
      push_cast
      field_simp
    have hkey : A * radiusSq ≤ 1 := by
      rw [hval, div_le_one hmR]
      -- 2μ₀·min·r·log ≤ 2μ₀·max·r·log ≤ β μ₀ max r log ≤ m
      have h2β : (2:ℝ) ≤ β := by linarith
      have hminmax : (↑(min n₁ n₂):ℝ) ≤ (↑(max n₁ n₂):ℝ) := by
        exact_mod_cast (min_le_max : min n₁ n₂ ≤ max n₁ n₂)
      have hb : 0 ≤ μ₀ * (↑(max n₁ n₂):ℝ) * (r:ℝ) * Real.log (↑(max n₁ n₂)) := by positivity
      have hbmin : 0 ≤ μ₀ * (r:ℝ) * Real.log (↑(max n₁ n₂)) := by positivity
      nlinarith [hdens, hb, hbmin, h2β, hminmax,
        mul_nonneg hb (by linarith : (0:ℝ) ≤ β - 2),
        mul_nonneg hbmin (sub_nonneg.mpr hminmax)]
    calc Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R
        = Real.sqrt (A * radiusSq) := by rw [hAdef] at hmerge ⊢; exact hmerge
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hkey
      _ = 1 := Real.sqrt_one
  have hExp := Hrad β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hRnn hdens_rad hprov hpt
  refine le_trans hExp ?_
  rw [hR]
  exact Hscale n₁ n₂ r m μ₀ hn1 hn2 hr hm hμ₀
