-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:43:23.896238+00:00
-- url     : https://prove2.me/theorems/3e8a840b-1807-45e7-a9e1-d615fc93d4d9
-- title:
--   Original stopped physical BV grid generator cell vanishes strictly below the positive optimal barrier
-- statement:
--   For the actual spectrally negative Lévy process and dividend strategy, the stopped deterministic physical-cell generator contribution of the optimal barrier candidate vanishes at every pre-ruin left prestate lying strictly between zero and the positive barrier. This directly specialises proved generator_vcstar_eq_zero and removes the near-origin generator-loss obstruction in that regime.
-- source:
--   Source-exact specialisation of Proved generator_vcstar_eq_zero 88d146b8 to the original stopped-leftlim physical grid. This result is only a strict prebarrier cell identity and does not claim global generator L1.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n i : ℕ) (ω : Ω) :
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ Z < (cstar W).toReal then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0 := by sorry
