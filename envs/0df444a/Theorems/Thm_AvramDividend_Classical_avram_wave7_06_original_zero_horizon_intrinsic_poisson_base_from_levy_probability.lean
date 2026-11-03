-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_from_levy_probability
-- name    : AvramDividend.Classical.avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_from_levy_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:20:46.058051+00:00
-- url     : https://prove2.me/theorems/7c2558e3-45ad-44d7-890e-6e8990cbe8d0
-- title:
--   Original Lévy negative-band Poisson void formula at zero horizon using source probability field
-- statement:
--   For the actual source process X on Ω, the intrinsic negative-band jump count at time zero vanishes. The SpectrallyNegativeLevy.isProbability field ensures P(Ω)=1, yielding the exact zero-horizon Poisson void formula without an extra probability normalisation assumption.
-- source:
--   Wave 7 Chat 06 exact boundary case of Open source marked-count law 390a8092-89ae-45c8-bed8-b43b900baa2f; no artificial Poisson process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_from_levy_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω |
       NX ω (Ioc 0 (0 : ℝ≥0) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
       ENNReal.ofReal (Real.exp
         (-((0 : ℝ) *
           (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) := by sorry
