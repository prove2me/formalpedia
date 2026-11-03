-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
-- name    : AvramDividend.Classical.avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:35:10.993047+00:00
-- url     : https://prove2.me/theorems/4bcce380-7041-4b9e-98bc-b445541026b8
-- title:
--   Original-source positive-cap right-endpoint discounted full Stieltjes value-drop bound with quantitative cell error
-- statement:
--   For any source spectrally negative Lévy process with genuine admissible dividend strategy and any pre-ruin interval, the entire original discounted dividend measure is controlled by the right-endpoint discount multiplied by the cap-linear source-frozen value drop plus q times cell width multiplied by the exact original Stieltjes mass. Covers zero and cap contacts, diffuse, singular-continuous and countably atomic payments, all positive finite or infinite caps. Provides the missing deterministic right-endpoint signed cell error for stopped source-grid refinement without assuming any stochastic martingale estimate.
-- source:
--   Direct original-source upgrade of canonically Proved quantitative right-endpoint arbitrary-measure estimate 4b1edf79... and Proved all-positive-cap source-frozen global secant and interval mass identities. Distinct from already Proved left-endpoint source bound d44e536f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_discounted_right_endpoint_cell_upper_error

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal
          (V (x + X.X b ω - rightLimit D a ω) -
            V (x + X.X b ω - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))) := by sorry
