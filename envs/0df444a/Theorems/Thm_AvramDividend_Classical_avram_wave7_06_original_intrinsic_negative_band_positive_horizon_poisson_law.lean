-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:37:03.549215+00:00
-- url     : https://prove2.me/theorems/aa265c9f-4568-4639-9694-5ab319ddc374
-- title:
--   Genuine original source negative-band Poisson zero-count law for positive horizons
-- statement:
--   For every strictly positive horizon T, the exact intrinsic marked jump count obtained from the original X.X and left limits has zero-count probability exp(-T ν(B)) on the original P space, for the negative cutoff band B. This is the remaining positive-horizon probabilistic theorem after the zero-horizon case is Proved.
-- source:
--   Exact positive-horizon hard child of source count law 390a8092-89ae-45c8-bed8-b43b900baa2f. This problem is left Open for genuine Poisson jump law derivation; no proof is being claimed by publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by sorry
