-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_of_probability_mass
-- name    : AvramDividend.Classical.avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_of_probability_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:48:21.493188+00:00
-- url     : https://prove2.me/theorems/9ada571b-8d39-4bb2-80d0-8be33328dbff
-- title:
--   Exact original negative-band Poisson zero-count formula at T=0 assuming P has unit mass
-- statement:
--   At T=0, the original intrinsic source negative-band counting measure is zero surely. If the original P has total mass one, its void probability equals exp(-0 times ν(B))=1, exactly the Poisson zero-count expression. The normalisation hP is explicitly assumed, not inferred from an arbitrary measure.
-- source:
--   Source-faithful base case of Open 390a8092-89ae-45c8-bed8-b43b900baa2f, showing the exact normalisation hypothesis needed at zero horizon, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_of_probability_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (hP : P Set.univ = 1) :
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
