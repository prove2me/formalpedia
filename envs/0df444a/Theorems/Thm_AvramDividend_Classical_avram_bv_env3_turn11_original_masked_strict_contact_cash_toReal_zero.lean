-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:57:41.414202+00:00
-- url     : https://prove2.me/theorems/5bc6b383-a2d7-4b36-9553-5fbe54134229
-- title:
--   Original strict stopped contact-tail cash vanishes in real-valued Fatou coordinates
-- statement:
--   The actual stopped original dividendMeasure weighted strict contact-tail integral tends to zero in real coordinates. Pass from the already proved ENNReal convergence using pinned Mathlib continuity of toReal at zero, preserving original paymentTimes and both stopping endpoints.
-- source:
--   Direct pinned-source consequence of Proved 7c53ca0f and Mathlib ENNReal.tendsto_toReal; supplies real-valued strict contact-error convergence for the P3-GRID3/P3-GRID4 Fatou bridge without replacing the original Lévy process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
      atTop (𝓝 (0 : ℝ)) := by sorry
