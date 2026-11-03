-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
-- name    : AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:41:36.894899+00:00
-- url     : https://prove2.me/theorems/eac4c5a9-1662-4aaf-b601-5a22768bcadc
-- title:
--   Exact second moment of original Levy finite-grid Borel marked increment occupancy
-- statement:
--   For the same original spectrally negative Levy process on Ω with P and its original filtration, the exact second moment of any finite Borel-marked occupation count of disjoint ordered deterministic increment cells is the sum of diagonal one-cell event probabilities and off-diagonal products of the two original cell probabilities. Every cross term is justified by source-filtration independence, using the newly Proved past-event two-separated-marked-cells factor theorem. The identity gives the elementary Bernoulli uniform-integrability input for approaching the actual intrinsic jump count; it neither assumes nor establishes the Levy intensity X.ν.
-- source:
--   Avram Wave6 Chat01, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Original source Bernoulli marked-increment second moment from elementary finite Tonelli, measurable source increment indicators and accepted source past-two-marked-cells joint probability product 7c4e6d15. Necessary uniform-integrability bridge towards intrinsic Lévy jump compensation; no proxy process or intensity premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
      ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i = j then
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
      else
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B} *
        P {ω | X.X (t (j + 1)) ω - X.X (t j) ω ∈ B} := by sorry
