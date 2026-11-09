-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
-- name    : AvramDividend.Classical.avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:37:25.434029+00:00
-- url     : https://prove2.me/theorems/f7a20a5c-cd93-4ab6-ac10-ad302c3c71e4
-- title:
--   Original zero-jump controlled prepayment reserve has its left limit at every positive clock simultaneously almost surely
-- statement:
--   For an original zero-jump spectrally negative Lévy process and any adapted monotone left-continuous dividend strategy, there is one full-measure set of paths on which the controlled pre-right-payment reserve equals its left limit at every strictly positive time, including path-dependent ruin and stopping clocks. This strengthens fixed-time almost-sure contact to random-time contact.
-- source:
--   Public Proved b462a147 gives global almost-sure continuity of original X. IsDividendStrategy supplies pathwise continuity from the left of D. The left-limit algebra follows the public fixed-horizon proof 50564343, with an AE event independent of t. Supports positive ruin terminal contact in original TOP 249c532d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        riskProcess X x D t ω := by sorry
