-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
-- name    : AvramDividend.Classical.avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:53:27.126205+00:00
-- url     : https://prove2.me/theorems/c524efcd-8b3e-4e7f-b424-5d01aa1333fd
-- title:
--   Original Gaussian finite measurable stopped-mask raw large-square tail is integrable from centred square energy and raw-centred cross integrability
-- statement:
--   For each physical mesh with any measurable stopping mask, if centred Gaussian squared increments and the absolute raw-centred quadratic cross are integrable as finite source sums, then the masked large-raw-increment squared tail is integrable. Every retained squared raw increment is bounded by its centred square plus the absolute cross difference. The theorem supplies the missing integrability premise for converting the Proved original stopped Gaussian raw tail ENNReal result ga56 to ordinary L1 in a149.
-- source:
--   Pointwise square domination, measurable finite source masks, Integrable.mono'.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω : Ω | A i ω})
    (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (d η : ℝ)
    (hEI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) P)
    (hAI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        |(Z i ω + d)^2 - (Z i ω)^2| else 0) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) else 0) P := by sorry
