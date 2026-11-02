-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
-- name    : AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:20:38.525309+00:00
-- url     : https://prove2.me/theorems/966471c3-2481-42f7-bf5d-a1007706b4c8
-- title:
--   Automatic finite-cap actual Stieltjes forward-secant integrability from time measurability
-- statement:
--   For an original admissible capped spectrally negative Levy dividend strategy with an explicit positive finite cap, the actual stopped finite-horizon Stieltjes integral of the derivative-free discounted forward secant residual is absolutely integrable whenever its composition is strongly measurable. The cap-linear extension gives a uniform magnitude bound and the original dividendMeasure has finite closed-horizon mass, including the true time-zero atom and singular-continuous variation. No reserve-interior localization or endpoint derivative is assumed.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
--   import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
--   import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- On any actual stopped finite dividend measure, the cap-linear forward
--   secant correction is automatically L1 once its time measurability is known.
--   Finite cap bounds the residual, and the genuine Stieltjes measure has finite
--   closed-horizon mass including the singular-continuous and zero atoms. -/
--   theorem AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
--       (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
--       (ω : Ω) (T : ℝ≥0)
--       (hMeas : AEStronglyMeasurable
--         (fun s : ℝ => Real.exp (-(q * s)) *
--         (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
--           V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
--         ((dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)))) :
--       IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
--         (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
--           V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
--         (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω) := by
--     let A : Set ℝ :=
--       paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)
--     let μ : Measure ℝ := (dividendMeasure D ω).restrict A
--     let f : ℝ → ℝ := fun s =>
--       Real.exp (-(q * s)) *
--         (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
--           V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))
--     let L : ℝ := (w C.toReal - C.toReal) - w 0
--     have hAmeas : MeasurableSet A :=
--       (paymentTimes_measurable _).inter measurableSet_Icc
--     have hA_sub : A ⊆ Icc (0 : ℝ) (T : ℝ) := by
--       intro s hs
--       exact hs.2
--     have hstrategy : IsDividendStrategy 𝓕 D := hD.1.1
--     have hμfinite : μ Set.univ < ⊤ := by
--       calc
--         μ Set.univ = (dividendMeasure D ω) A := by simp [μ]
--         _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) :=
--           measure_mono hA_sub
--         _ = ENNReal.ofReal (rightLimit D T ω) :=
--           avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hstrategy ω T
--         _ < ⊤ := ENNReal.ofReal_lt_top
--     letI : IsFiniteMeasure μ := (isFiniteMeasure_iff μ).2 hμfinite
--     have hBound : ∀ s : ℝ, s ∈ A → ‖f s‖ ≤ L := by
--       intro s hs
--       have hsPay := hs.1
--       change s ∈ Ici (0 : ℝ) ∩
--         ({0} ∪ {t : ℝ | ENNReal.ofReal t < ruinTime X x D ω}) at hsPay
--       have hPreS : s.toNNReal = 0 ∨
--           (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
--         rcases hsPay.2 with hzero | hlt
--         · left
--           have heq : s = 0 := by simpa using hzero
--           simp only [heq, Real.toNNReal_zero]
--         · right
--           change (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hlt
--           exact hlt
--       have hCover := hD.1.2 ω s.toNNReal hPreS
--       dsimp [riskProcess] at hCover
--       let y : ℝ := x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
--       have hy : 0 ≤ y := by linarith only [hCover]
--       have hSec := avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
--         C hC hCfinite w V hw_cont hw_smooth hw_grad hVfinite
--         y δ hy hδ
--       let R : ℝ := δ + V y - V (y + δ)
--       have hRhi : R ≤ 0 := by
--         dsimp [R]
--         linarith only [hSec.1]
--       have hRlo : -L ≤ R := by
--         dsimp [R, L]
--         linarith only [hSec.2]
--       have hExpLe : Real.exp (-(q * s)) ≤ 1 := by
--         have hn : -(q * s) ≤ (0 : ℝ) :=
--           neg_nonpos.mpr (mul_nonneg hq hsPay.1)
--         simpa using (Real.exp_le_exp.mpr hn)
--       have hAbs : |Real.exp (-(q * s)) * R| =
--           Real.exp (-(q * s)) * (-R) := by
--         rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonpos hRhi]
--         ring
--       change |Real.exp (-(q * s)) * R| ≤ L
--       rw [hAbs]
--       calc
--         Real.exp (-(q * s)) * (-R) ≤ 1 * (-R) :=
--           mul_le_mul_of_nonneg_right hExpLe (neg_nonneg.mpr hRhi)
--         _ = -R := by ring
--         _ ≤ L := by linarith only [hRlo]
--     change Integrable f μ
--     have hAES : AEStronglyMeasurable f μ := hMeas
--     apply Integrable.of_bound hAES L
--     filter_upwards [ae_restrict_mem hAmeas] with s hs
--     exact hBound s hs

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      ((dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)))) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω) := by sorry
