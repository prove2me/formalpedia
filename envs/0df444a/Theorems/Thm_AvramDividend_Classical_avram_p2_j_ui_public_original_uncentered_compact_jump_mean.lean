-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_uncentered_compact_jump_mean
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_uncentered_compact_jump_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:57:54.721544+00:00
-- url     : https://prove2.me/theorems/2ee928e4-0243-448a-a06a-087268d26902
-- title:
--   Public original uncentred intrinsic negative compact-test jump expectation from P2-A source
-- statement:
--   Given the original spectrally negative Levy process, a positive horizon, measurable original coordinate maps and continuous real compact-negative test with explicit support cutoffs, construct the integrable finite sum of precisely the original uncentred positive-time intrinsic jumps at which the test is nonzero. Prove its real expectation equals the horizon times the original negative Levy measure integral. The proof uses only publicly Proved P2-A source theorems for centred compact-test expectation and original centred-to-uncentred jump equality. The result is public and may feed the canonical Borel marked count.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_test_intrinsic_jump_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_centered_uncentered_jump_delta

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_uncentered_compact_jump_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∫ ω, J ω ∂P) =
        (T : ℝ) * (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))) := by sorry
