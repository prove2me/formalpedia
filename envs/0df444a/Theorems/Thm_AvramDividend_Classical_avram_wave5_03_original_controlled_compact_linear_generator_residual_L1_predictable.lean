-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
-- name    : AvramDividend.Classical.avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:27:04.794038+00:00
-- url     : https://prove2.me/theorems/fbf81db0-c3c9-4377-aeed-72f77ec73cbe
-- title:
--   Original compact source linear Lévy drift and discount value residual are integrable on the same finite predictable clock
-- statement:
--   For the identical original SpectrallyNegativeLevy X, full-variation adapted dividend strategy D and strongly predictable prepayment left-limit reserve, compact C2 localisation yields genuine finite expected first moments for the Lévy linear drift c w' and discounted value residual -q w against every finite right-continuous predictable clock. The test function need only be C2 on the open interior; it may be zero-extended or irregular outside, including negative reserves. This is the complementary linear hJ ingredient to 03-B full nonlinear source jump drift and 03-A Gaussian curvature, enabling the full original discounted generator residual L1 bridge into Proved 732738fd and the corrected UBV stochastic core.
-- source:
--   Original source corrected UBV 429e17ca; Proved original left-limit predictability 94ee9994; Proved 04-B compact masked gradient bcd9edf0; Proved compact derivative uniform bound; pinned compact-continuous maximum theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (q : ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Integrable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then X.c * deriv w (Y p) - q * w (Y p)
      else 0) μ := by sorry
