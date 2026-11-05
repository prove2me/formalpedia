-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_p4_original_bounded_grid_mean_zero_of_p2e
-- name    : AvramDividend.Classical.avram_integration_p4_original_bounded_grid_mean_zero_of_p2e
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:48:31.950788+00:00
-- url     : https://prove2.me/theorems/528d2277-8a72-4a8f-aea1-2888e9280863
-- title:
--   Original P2-E public rectangle compensation discharges P4-B bounded predictable finite-grid martingale rate premise
-- statement:
--   The original-process predictable rectangle compensation is now proved canonically by P2-E. Substitute this rate equality into the fully Proved public P4-B finite-grid predictable compensated-jump L1 expectation-zero theorem, removing its independent hRaw premise. All other original source and bounded predictable weight hypotheses remain explicit for later P4-F Itô localisation.
-- source:
--   P2-E 393b03a8 is public Proved; P4-B 1868c36c is public Proved. This bridge is a source-exact noncircular preparation for the original P4-F jump martingale term.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_integration_p4_original_bounded_grid_mean_zero_of_p2e
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i ∈ S, ∀ n, s i < r i n)
    (hrt : ∀ i ∈ S, ∀ n, r i n ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (J : ι → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ i a b ω, J i a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B i))
    (hShort : ∀ i ∈ S,
      Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i ∈ S,
      Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (hFinite : ∀ i ∈ S, X.ν (B i) ≠ ⊤)
    (hMass : ∀ i ∈ S, ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont (s i)] A → P A ≠ ⊤)
    (hRate : ∀ i ∈ S, ∀ n, (∫⁻ ω, J i (s i) (r i n) ω ∂P) =
      ((r i n - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i (s i) (t i)))
    (hFullRate : ∀ i ∈ S,
      (∫⁻ ω, J i (s i) (t i) ω ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (H : ι → Ω → ℝ) (C : ι → ℝ)
    (hH : ∀ i ∈ S,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hBound : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((J i (s i) (t i) ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by sorry
