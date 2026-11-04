-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_signed_predictable_real_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_signed_predictable_real_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:00:10.11824+00:00
-- url     : https://prove2.me/theorems/11609f5e-719e-4985-8a5d-8d00914e419a
-- title:
--   Finite signed predictable-simple original Lévy jump-count integrands have exact real expectation
-- statement:
--   On the actual original process and filtration, finite sums of signed predictable rectangle weights, each a difference of two finite-mean nonnegative Fs weights, are real L1. Their expectation is the sum of the corresponding signed prescribed Levy rate factors, assuming each original-process unconditional rate as an explicit hypothesis. This is the finite signed simple-integrand compensation step for BV/UBV.
-- source:
--   Accepted P2-E signed original past-weighted real rate fc91754b and pinned Mathlib integrable_finset_sum/integral_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_signed_past_weighted_real_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_signed_predictable_real_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (Wpos Wneg : ι → Ω → ℝ≥0∞)
    (hWp : ∀ i ∈ S, Measurable[𝓕 (s i)] (Wpos i))
    (hWn : ∀ i ∈ S, Measurable[𝓕 (s i)] (Wneg i))
    (hFp : ∀ i ∈ S, (∫⁻ ω, Wpos i ω ∂P) < ⊤)
    (hFn : ∀ i ∈ S, (∫⁻ ω, Wneg i ω ∂P) < ⊤)
    (hν : ∀ i ∈ S, X.ν (B i) < ⊤)
    (hRate : ∀ i ∈ S, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P) =
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    let J : ι → Ω → ℝ := fun i ω =>
      (Wpos i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal -
      (Wneg i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal
    let rate : ι → ℝ := fun i => (((∫⁻ ω, Wpos i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal -
    ((∫⁻ ω, Wneg i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    Integrable (fun ω => ∑ i ∈ S, J i ω) P ∧
      (∫ ω, ∑ i ∈ S, J i ω ∂P) = ∑ i ∈ S, rate i := by sorry
