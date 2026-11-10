-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_ledger16_original_positive_reserve_two_sided_local_floor
-- name    : AvramDividend.Classical.avram_gauss_ledger16_original_positive_reserve_two_sided_local_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:40:49.596238+00:00
-- url     : https://prove2.me/theorems/c5dabfd5-5d41-4136-99e4-211d4a9a56b2
-- title:
--   Original positive postpayment reserve has a two-sided local spatial floor
-- statement:
--   For the same original X and dividend strategy D, at any positive postpayment reserve value within a finite interval, there is a strictly positive deterministic spatial lower floor on a relative two-sided neighbourhood of that time. This follows from the Proved pathwise upper semicontinuity of the negative original postpayment reserve and handles clock approaches from the left, a distinct boundary requirement for Gaussian lower-exit localisation 3308ae9d.
-- source:
--   Necessary original-process topological boundary ingredient for the accepted Gaussian floor-localisation route through 3308ae9d; use Proved 5b13a627 negative postpayment upper semicontinuity.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gauss_ledger16_original_positive_reserve_two_sided_local_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0)
    (ht : t ∈ Set.Icc 0 T)
    (hPositive : 0 < x + X.X t ω - rightLimit D t ω) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ s in 𝓝[Set.Icc 0 T] t,
        δ ≤ x + X.X s ω - rightLimit D s ω := by sorry
