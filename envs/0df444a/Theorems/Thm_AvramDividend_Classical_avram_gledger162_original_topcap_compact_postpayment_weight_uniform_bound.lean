-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
-- name    : AvramDividend.Classical.avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:20:11.802148+00:00
-- url     : https://prove2.me/theorems/f91d1501-2c24-486f-b169-9e034ff89f68
-- title:
--   Original Gaussian postpayment compact-band weights have a uniform deterministic bound
-- statement:
--   Proves a deterministic uniform bound on the original postpayment w(Y(t)) for every actual physical time strictly preceding clipped rho, using only source gledger137 compact prefix band and original top-cap local C2 smoothness; needed to instantiate finite weighted Euler bound gledger149 for gledger161, without any global bound at zero.
-- source:
--   Original physical gledger137 prefix band and compact boundedness of continuous w over positive compact Icc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      |w (x + X.X t ω - rightLimit D t ω)| ≤ K := by sorry
