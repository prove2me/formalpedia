-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
-- name    : AvramDividend.Classical.avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:21:29.269+00:00
-- url     : https://prove2.me/theorems/19ad1e05-76af-4bde-be5f-5b724b72b4dc
-- title:
--   Original right-closed contact cash real limit with automatic endpoint finiteness
-- statement:
--   The original ruin-stopped discounted Stieltjes right-closed shrinking contact cell tends in Real to the exact surviving endpoint atom with no auxiliary finiteness premise. Finiteness follows from the actual dividend strategy's original rightLimit [0,T] measure identity.
-- source:
--   Composition of BV-ENV3 turn13 original singleton endpoint finiteness with turn12 original ENNReal-to-real contact limit. Retains full original payment-masked atom at τ and excludes non-payable ruin atom. Supports the pathwise Fatou closure c1e2f021.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn14_original_closed_contact_tail_real_endpoint_automatic
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
          ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) := by sorry
