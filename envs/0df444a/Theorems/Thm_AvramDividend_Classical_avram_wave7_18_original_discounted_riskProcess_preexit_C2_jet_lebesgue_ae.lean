-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae
-- name    : AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:22:52.080472+00:00
-- url     : https://prove2.me/theorems/3cd868d7-ba85-4bf1-92c7-c99c39b7f335
-- title:
--   Discounted actual original riskProcess C² jets are bounded a.e. before interior exit
-- statement:
--   For the actual original Lévy riskProcess and original dividend strategy, with q>0 and the exact positive-cap ContDiffOn ℝ 2 source hypothesis, show that the discounted C² jet exp(-q t) times w, w′ and w″ evaluated at riskProcess remains bounded by a deterministic constant for Lebesgue-almost-every nonnegative real t strictly below the genuine original-filtration dense-grid first-exit clock. Import the Proved discounted post-payment stopped bound and the Proved original riskProcess/post-payment Lebesgue-a.e. equality. No assertion is made at simultaneous right-payment jumps, ruin or finite-cap exit, and C=∞ is supported.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_lebesgue_ae
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
        ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
          0 ≤ t → t.toNNReal < T →
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             w (riskProcess X x D t.toNNReal ω)| ≤ M ∧
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             deriv w (riskProcess X x D t.toNNReal ω)| ≤ M ∧
          |Real.exp (-(q * (t.toNNReal : ℝ))) *
             deriv (deriv w) (riskProcess X x D t.toNNReal ω)| ≤ M := by sorry
