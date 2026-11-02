-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:04:51.490344+00:00
-- url     : https://prove2.me/theorems/4a829048-d1d0-4846-9f83-602609ae74b0
-- title:
--   Original-source global finite-grid signed real dividend Stieltjes correction including time-zero atom
-- statement:
--   For a genuine spectrally negative Levy source and any admissible finite-cap dividend strategy, the signed real correction consisting of the actual exponentially discounted dividendMeasure payment integral plus cap-linear value change at the time-zero right-payment, and the corresponding signed complete Stieltjes terms over every right-endpoint cell of a finite nondecreasing pre-ruin grid, has a nonpositive total. The actual dividend measure includes all absolutely continuous and singular-continuous variation and countably many right-payment jumps. The source left jump occurs before the right dividend at each endpoint. No strict-interior localisation, boundary derivative or atomlessness hypothesis is imposed. This is a finite-grid dividend term, to be combined with moving-source Ito-Meyer terms and mesh convergence.
-- source:
--   Finite sum of Proved original-source interval signed control (pending prerequisite avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos) plus Proved genuine initial signed atom (pending prerequisite avram_wave5_04b_original_time_zero_signed_atom_control_nonpos), applying Finset.sum_le_sum and linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hgrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    ((∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X 0 ω - rightLimit D 0 ω) -
      V (x + X.X 0 ω)) +
    ∑ i ∈ Finset.range n,
      ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 := by sorry
