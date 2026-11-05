-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
-- name    : AvramDividend.Classical.avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:18:00.526093+00:00
-- url     : https://prove2.me/theorems/fe93668b-f509-4eeb-82a9-0af609cdb4cd
-- title:
--   Original controlled reserve compact value is predictable with finite local quadratic energy
-- statement:
--   For the genuine original spectrally negative Levy source with an adapted dividend strategy, form the strict left-limit Y of x+X.X-rightLimit D, which is strongly predictable in the original right-continuous filtration. If w is C2 on the exact positive interior {y | 0<y and ENNReal.ofReal y<C}, then on every compact band [u,v] lying strictly inside a larger positive cap-admissible band (a,b), the masked candidate value V=1_{Y in [u,v]} w(Y) is predictable-measurable and has finite squared energy against any finite predictable measure. The proof composes the source left-limit predictability with the measurable zero extension of an interior continuous function and uses its compact uniform bound. This is true for C finite under hband and for C=top; it makes no global unbounded-reserve L2 claim.

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let V : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] V ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((V p) ^ 2) ∂μ) < ⊤ := by sorry
