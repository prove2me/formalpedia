-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_measurable_real_sequence_limit_default_20261113
-- name    : AvramDividend.Classical.avram_a23_measurable_real_sequence_limit_default_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:16:24.642883+00:00
-- url     : https://prove2.me/theorems/93b57469-2652-4144-8757-e41205430c31
-- title:
--   Borel default limit of real measurable source functionals agrees with every actual pointwise limit
-- statement:
--   For any measurable domain, the pointwise default-valued limit of countably many measurable real-valued functions is measurable and equals the true pointwise limit wherever it exists; there is no probability-space completion requirement.
-- source:
--   Pinned Mathlib MeasureTheory.StronglyMeasurable.limUnder and Filter.Tendsto.limUnder_eq; A23 original Gaussian source measurable-cutoff limit.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

/-- The default-valued limit of countably many measurable real-valued functionals is measurable and coincides with every actual limit. -/

theorem AvramDividend.Classical.avram_a23_measurable_real_sequence_limit_default_20261113
    {X : Type*} [MeasurableSpace X]
    (W : ℕ → X → ℝ) (hW : ∀ n, Measurable (W n)) :
    ∃ Wlim : X → ℝ,
      Measurable Wlim ∧
      ∀ x : X, ∀ r : ℝ,
        Tendsto (fun n : ℕ => W n x) atTop (𝓝 r) →
          Wlim x = r := by sorry
