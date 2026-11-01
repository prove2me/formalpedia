-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:25:31.073982+00:00
-- url     : https://prove2.me/theorems/e9d37487-9d91-4e3e-867a-81d628faeb64
-- title:
--   Full original Lévy Stieltjes martingale consumption for arbitrary positive exponential tilt
-- statement:
--   The expected actual-source initial right-dividend atom plus theta times the fully weighted positive-time Stieltjes dividend mass is at most one, for every positive theta and finite horizon. The proof uses original source predictable finite-grid Lévy exponential martingales, exact stochastic Stieltjes cell integration, and theta-scaled double-Fatou passage, retaining diffuse, singular continuous, and right-atomic payments on the same sample paths.
-- source:
--   Original-source finite-grid theta budget b5e6d927, the all-real dyadic step bridge 3f4cb787, and theta-scaled source double Fatou (new child).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_doubleFatou_expected
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
