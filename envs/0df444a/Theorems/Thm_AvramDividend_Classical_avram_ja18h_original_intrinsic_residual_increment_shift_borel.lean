-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_intrinsic_residual_increment_shift_borel
-- name    : AvramDividend.Classical.avram_ja18h_original_intrinsic_residual_increment_shift_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:27:06.786626+00:00
-- url     : https://prove2.me/theorems/1afff3a2-9677-430e-a005-480629fbb498
-- title:
--   Original residual future increment factors through a Borel functional of the shifted original Lévy path
-- statement:
--   At fixed s≤t on the original probability space, the physical intrinsic finite-cutoff-zero residual difference admits a Borel measurable real functional W of the entire original future increment path u↦X(s+u)−X(s), with pointwise equality. Construct W from the raw shifted path and the exactly shifted signed small-band and large-band jump measures. Existing proved original negative-band shift identities 238b5785 and 613d1237 supply the pathwise stochastic ledger. No auxiliary Brownian process.
-- source:
--   AVRAM J-A18 original filtration intrinsic residual shifted path factorisation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18h_original_intrinsic_residual_increment_shift_borel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
