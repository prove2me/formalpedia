-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
-- name    : AvramDividend.Classical.avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:55:43.956774+00:00
-- url     : https://prove2.me/theorems/a23ab0a4-f5bc-4543-b254-9466b3396124
-- title:
--   Original pre-exit Gaussian derivative coefficients remain uniformly bounded under the exact ruin indicator
-- statement:
--   For the actual original controlled zero-jump Lévy reserve up to its countably observed compact-band exit, the discounted Gaussian gradient and interior-gated Hessian remain uniformly bounded after multiplication by the original ruin-time indicator. The result gives the exact two stochastic-integrand coefficient shapes required by the Proved original full stopped Gaussian L1 mean-zero theorem, retaining the original path and true left-limit expressions, rather than assumed surrogate coefficients.
-- source:
--   Source-exact nonanticipative ruin indicator coefficient bridge for the two coefficients of publicly Proved 94037a94; imports only the F17 original true-left-limit gated bound, not any canonical ancestor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          |(Real.exp (-(q * (t : ℝ))) * deriv w y) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)| ≤ KG ∧
          |(Real.exp (-(q * (t : ℝ))) *
            (if 0 < y ∧ ENNReal.ofReal y < C
             then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)| ≤ KH := by sorry
