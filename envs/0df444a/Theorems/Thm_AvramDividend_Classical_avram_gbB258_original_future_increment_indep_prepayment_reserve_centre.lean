-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
-- name    : AvramDividend.Classical.avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:54:26.7632+00:00
-- url     : https://prove2.me/theorems/3db72820-9dd7-4ccb-a645-50fb790e9fe2
-- title:
--   Original Levy future increment independent of actual adapted prepayment reserve interval centre
-- statement:
--   For any genuine original spectrally negative Levy source and an admissible dividend strategy adapted to the original filtration, the future source increment over s to t is independent of the random prepayment reserve centre b-x-X(s)+D(s), for every deterministic s less than or equal to t. The centre measurability follows from the actual original filtration-adapted source and dividend. This is the exact filtration independence required to apply conditional Gaussian small-ball estimates to arbitrary adapted dividend controls, without assuming the controlled reserve itself has Gaussian marginal law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (x b : ℝ) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (MeasurableSpace.comap (fun ω => b - x - X.X s ω + D s ω) inferInstance) P := by sorry
