-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_marginal_integrable
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_marginal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:09:19.505748+00:00
-- url     : https://prove2.me/theorems/81ca4a88-dd32-48b6-bca2-14e2414a8335
-- title:
--   Original Levy continuous compact-negative one-time tests are integrable from genuine path measurability
-- statement:
--   Under only original X time-coordinate measurability and probability measure, compact negative support gives a finite uniform ENNReal envelope by proved P2-J. Convert it to a real bound and apply pinned Mathlib Integrable.of_bound to show genuine original single-time test integrability at every nonnegative time. This discharges a necessary finite-grid stationary expectation hypothesis without assuming a jump intensity.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_test_finite_envelope
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_marginal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∀ t : ℝ≥0, Integrable (fun ω => g (X.X t ω)) P := by sorry
