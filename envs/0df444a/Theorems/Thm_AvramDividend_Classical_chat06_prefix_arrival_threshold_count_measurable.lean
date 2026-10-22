-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_prefix_arrival_threshold_count_measurable
-- name    : AvramDividend.Classical.chat06_prefix_arrival_threshold_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:02:59.688979+00:00
-- url     : https://prove2.me/theorems/c2e4502a-f6af-4345-8e91-d0ecf6249aaa
-- title:
--   Finite interarrival-prefix threshold count is measurable
-- statement:
--   For any fixed count cutoff n and observation time s, count the indices k<n whose first k+1 waiting-time coordinates sum to at most s. This is a measurable function of the full waiting-time sequence: express the finite filtered-set cardinality as a finite sum of natural-valued indicators of measurable partial-sum threshold events. Finite sums and measurable if-then-else functions preserve measurability. This gives the measurable prefix-to-count map used for constructing the natural counting-process history.
-- source:
--   bv_prefix_arrival_threshold_count_measurable_v2_chat06_20261021.lean, 34 lines, 1312 bytes, SHA-256 4112ebcaa104909349449420178618fea4ab38d980bc51cae73e00b81064dbc5; private probe 8aad961b-87e9-4f68-90e9-ce4d7caaf776 reached sentinel with no source errors.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory

theorem AvramDividend.Classical.chat06_prefix_arrival_threshold_count_measurable (n : ℕ) (s : ℝ) :
    Measurable (fun z : ℕ → ℝ =>
      ((Finset.range n).filter (fun k =>
        (∑ i ∈ Finset.range (k + 1), z i) ≤ s)).card) := by sorry
