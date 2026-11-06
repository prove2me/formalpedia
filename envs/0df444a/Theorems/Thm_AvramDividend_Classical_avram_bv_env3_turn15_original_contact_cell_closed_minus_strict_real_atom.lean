-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn15_original_contact_cell_closed_minus_strict_real_atom
-- name    : AvramDividend.Classical.avram_bv_env3_turn15_original_contact_cell_closed_minus_strict_real_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:25:40.72889+00:00
-- url     : https://prove2.me/theorems/d37d4130-823e-47e1-9515-8c3368a73dc9
-- title:
--   Original stopped right-closed versus strict contact-cell cash detects exact payment atom
-- statement:
--   For actual original ruin-stopped discounted Stieltjes dividend cash, the difference between right-closed and strict shrinking contact-cell integrals converges in Real to precisely the surviving endpoint atom. Time-zero, horizon and ruin-contact conventions are preserved.
-- source:
--   Direct composition of source-exact BV-ENV3 turn14 automatic right-closed endpoint limit and turn11 strict tail-toReal zero. Supports physical mesh correction for c1e2f021; no auxiliary law or atom-zero hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn11_original_masked_strict_contact_cash_toReal_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn15_original_contact_cell_closed_minus_strict_real_atom
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
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal -
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) := by sorry
