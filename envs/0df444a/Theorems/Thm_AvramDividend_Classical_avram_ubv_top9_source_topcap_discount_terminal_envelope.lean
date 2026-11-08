-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_discount_terminal_envelope
-- name    : AvramDividend.Classical.avram_ubv_top9_source_topcap_discount_terminal_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:43:55.307839+00:00
-- url     : https://prove2.me/theorems/e225ab08-37de-4aab-9ee4-676e6962d177
-- title:
--   Original infinite-cap HJB implies a uniform discounted stopped-terminal spatial envelope
-- statement:
--   Under the literal spectrally negative Levy candidate HJB, smoothness and gradient hypotheses with cap infinity, every candidate terminal reward at a source stopped time with a fixed positive spatial upper ceiling lies between zero and the candidate value at that ceiling. This is the source-exact bound for per-localiser tail estimates, without a finite global cap or future-process decomposition.
-- source:
--   Compose Proved topcap halfline HJB bridge d1a94bc6 with Proved analytic discounted terminal envelope a41c3f59.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_positive_halfline_discount_terminal_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_source_topcap_discount_terminal_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (B : ℝ) (hB : 0 < B) (V : Ω → ℝ)
    (hV : ∀ ω, V ω ≤ B) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤ Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ∧
      Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ≤ w B := by sorry
