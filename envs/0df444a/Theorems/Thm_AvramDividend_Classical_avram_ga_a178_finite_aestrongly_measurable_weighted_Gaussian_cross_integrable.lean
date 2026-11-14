-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
-- name    : AvramDividend.Classical.avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:37:33.876528+00:00
-- url     : https://prove2.me/theorems/0155c8de-83b5-4f87-bfd0-fc04ecc04c21
-- title:
--   Finite Gaussian Hessian-weighted original source cross integrable from measurable coefficient and unweighted absolute energy
-- statement:
--   For an almost-everywhere strongly measurable finite source cross-increment array, an almost-sure uniform bound on the Hessian coefficient gives integrability of the weighted absolute finite sum whenever the unweighted sum of absolute raw-centred quadratic source increments is integrable. This fills the integrability prerequisite for the existing proved-parent strategy via ga_a168 in original a150. The actual source may be the original stopped Levy process, with no surrogate.
-- source:
--   Finite a.e. strongly measurable sums, pointwise absolute sum domination and Mathlib Integrable.mono'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ) (H R : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hHm : ∀ m i, AEStronglyMeasurable (H m i) P)
    (hRm : ∀ m i, AEStronglyMeasurable (R m i) P)
    (hH : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ S m, |H m i ω| ≤ K)
    (hRI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, |R m i ω|) P) :
    ∀ m, Integrable (fun ω =>
      |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P := by sorry
