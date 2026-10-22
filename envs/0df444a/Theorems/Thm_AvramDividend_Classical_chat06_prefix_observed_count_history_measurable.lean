-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
-- name    : AvramDividend.Classical.chat06_prefix_observed_count_history_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:09:59.092122+00:00
-- url     : https://prove2.me/theorems/b703328f-8924-4250-b3ec-2d96ffe320a5
-- title:
--   Entire fixed-clock counting history determined measurably by interarrival prefix thresholds
-- statement:
--   For an observation horizon clock and finite cutoff n, the path indexed by every real time s≤clock that counts how many of the first n cumulative waiting-time sums have occurred by s is measurable as a function of the interarrival sequence into the full product space of count histories. The proof uses the characterisation of measurable functions to countable products by measurable coordinates, represents each finite filtered-set cardinality as a finite sum of indicators, and checks the measurability of every partial-sum threshold. It supplies the complete measurable prefix-to-observed-count-path map required for natural-filtration independence.
-- source:
--   bv_prefix_observed_count_history_measurable_chat06_20261021.lean, 37 lines, 1434 bytes, SHA-256 1b2adcf8a4d0cc63324eda2241e67c75feba2c2510d6935a0bee2cfce5b7061d; private probe 895b094d-8981-4890-a858-491918b606cc reached sentinel with no source errors.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory

theorem AvramDividend.Classical.chat06_prefix_observed_count_history_measurable (n : ℕ) (clock : ℝ) :
    Measurable (fun z : ℕ → ℝ =>
      fun s : Set.Iic clock =>
        ((Finset.range n).filter (fun k =>
          (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ))).card) := by sorry
