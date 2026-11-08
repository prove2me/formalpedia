-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
-- name    : AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:38:25.132276+00:00
-- url     : https://prove2.me/theorems/8846543e-4827-4d02-97d2-5e5b6987fba7
-- title:
--   Original BV full drift and residual sum is measurable on arbitrary deterministic grids
-- statement:
--   For the actual bounded-variation spectrally negative Levy X and admissible dividend D, the full signed generator and intrinsic raw-removed residual finite sum B is AE strongly measurable on every deterministic grid u, without uniform-spacing or rational-grid hypotheses. Only measurability of the value test and original generator are required. This certifies the precise B expression in the open original physical stopped residual theorem 4f851376, where the prescribed grid is arbitrary and the existing uniform-only source cb4b8ca1 is insufficient.
-- source:
--   Direct source-exact derivation from the original controlled prestate ambient measurability c5058357, ruinTime_measurable bbfbecf4 and the true original raw R coordinate AE measurability 86c7cf52. Generator Borel is an explicitly stated honest hypothesis, independently supplied by pending BV-MEAS7 grid-free original-generator child. Each masked generator cell is measurable and each intrinsic R-cell is AE measurable, yielding the finite sum. No process proxy, equality in law or integrability assumption is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w)
    (hGen : Measurable (fun y : ℝ => X.generator w y))
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n, AEStronglyMeasurable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1))))) P := by sorry
