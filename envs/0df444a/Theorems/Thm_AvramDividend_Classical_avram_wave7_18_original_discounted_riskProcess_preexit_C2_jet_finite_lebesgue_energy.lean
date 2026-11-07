-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy
-- name    : AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:54:03.114218+00:00
-- url     : https://prove2.me/theorems/fa96812e-75db-4faa-b1a4-670f5c6bfb71
-- title:
--   Discounted original riskProcess pre-exit C² jets have finite Lebesgue energy on any finite time window
-- statement:
--   Under the exact C²-on-positive-interior hypothesis and positive discount q, reuse the Proved original-riskProcess discounted w, w′, w″ bounds almost everywhere strictly before the original dense-grid bounded interior-exit clock. On an arbitrary measurable finite-Lebesgue-volume time set A contained in nonnegative pre-exit times, each absolute discounted jet is bounded by M almost everywhere. Their sum is bounded by 3M, so its ENNReal indicator lintegral is finite by lintegral_mono_ae and lintegral_indicator_const. This is dt-integrability for the actual controlled reserve, not dividend Stieltjes measure integrability; boundary hitting, stopped martingale compensation, and C² at the cap are separate obligations.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ (A : Set ℝ), MeasurableSet A →
          (volume : Measure ℝ) A < ⊤ →
          (∀ t ∈ A, 0 ≤ t ∧ t.toNNReal < T) →
          let E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
            (|Real.exp (-(q * (t.toNNReal : ℝ))) *
                w (riskProcess X x D t.toNNReal ω)| +
              |Real.exp (-(q * (t.toNNReal : ℝ))) *
                deriv w (riskProcess X x D t.toNNReal ω)| +
              |Real.exp (-(q * (t.toNNReal : ℝ))) *
                deriv (deriv w) (riskProcess X x D t.toNNReal ω)|)
          (∫⁻ t : ℝ, A.indicator E t ∂(volume : Measure ℝ)) < ⊤ := by sorry
