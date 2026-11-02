-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:58:27.466198+00:00
-- url     : https://prove2.me/theorems/d75d69ba-9467-4d61-86cd-c3bb1b09a085
-- title:
--   Unclipped original solvent reserve actual Stieltjes real signed boundary secant integral
-- statement:
--   For an original spectrally negative Lévy controlled reserve whose actual postpayment state is nonnegative throughout a closed horizon, and at every positive cap C (finite or infinite), the real integrable signed Stieltjes integral of discounted forward secant residual δ+V(Y_s)-V(Y_s+δ) against the actual dividendMeasure D omega is nonpositive. Y_s is the unclipped genuine source-X postpayment reserve. The non-strict solvency assumption allows Y_s=0 or cap and is weaker than old strict-interior hloc. Singular-continuous, diffuse, countable atoms, and t=0 are included. This proves sign of the regularised control integrand but does not by itself identify the Ito-Meyer finite variation term.
-- source:
--   import Mathlib
--   import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
--   import Definitions.Def_AvramDividend_Classical_DividendStrategy
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- At genuinely solvent original source-X postpayment states, the actual real
--   Stieltjes signed forward-secant correction is nonpositive on the full closed
--   horizon, including boundary contacts and singular-continuous variation. -/
--   theorem solution
--       {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
--       {𝓕 : Filtration ℝ≥0 mΩ}
--       (X : SpectrallyNegativeLevy P 𝓕)
--       (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
--       (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
--       (hSolvent : ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
--         0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)
--       (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
--         (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
--       (∫ s in Icc (0 : ℝ) (T : ℝ),
--         Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by
--     have hPoint : ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
--         Real.exp (-(q * s)) *
--           (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ≤ 0 := by
--       intro s hs
--       let y : ℝ := x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
--       have hy : 0 ≤ y := hSolvent s hs
--       have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ.le
--       have hSec := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--         C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--         y (y + δ) hy hOrder
--       have hResidual : δ + V y - V (y + δ) ≤ 0 := by
--         linarith only [hSec]
--       exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
--     apply MeasureTheory.integral_nonpos_of_ae
--     filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
--     exact hPoint s hs

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos

    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hSolvent : ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
      0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω)
    (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Icc (0 : ℝ) (T : ℝ),
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by sorry
