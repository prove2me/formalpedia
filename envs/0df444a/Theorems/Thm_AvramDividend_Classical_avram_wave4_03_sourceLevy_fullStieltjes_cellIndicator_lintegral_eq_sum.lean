-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:32:34.649208+00:00
-- url     : https://prove2.me/theorems/cc6c2317-7033-4977-9516-f6e8c89de593
-- title:
--   Exact original Lévy source weighted full Stieltjes finite-cell integral equals random dividendMeasure cell-mass sum
-- statement:
--   On each actual original spectrally negative Lévy sample path and any dividend strategy path, the Stieltjes integral of the finite sum of right-grid cell indicators weighted by the original compensated exponential and the actual postpayment discount equals the sum of these same source weights multiplied by the full Stieltjes dividendMeasure of each Ioc cell. The equality retains diffuse and singular-continuous payments and each right dividend atom.
-- source:
--   Pinned Mathlib lintegral_finset_sum and lintegral_indicator_const applied directly to actual X and random dividendMeasure D; source stochastic expected budget 3397f585 provides intended downstream consumer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ) (u : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      ENNReal.ofReal (θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) *
      dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ)) := by sorry
