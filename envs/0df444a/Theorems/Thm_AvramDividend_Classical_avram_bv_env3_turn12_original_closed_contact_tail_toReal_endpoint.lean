-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:58:49.515597+00:00
-- url     : https://prove2.me/theorems/291ea9b4-e4a5-471a-ad80-319651bb4c65
-- title:
--   Original closed stopped contact-tail toReal limit equals the endpoint atom
-- statement:
--   For the actual dividendMeasure of the original Lévy model, right-closed stopped contact-tail cash converted to Real converges to the precise surviving singleton payment atom. The source is the already Proved original ENNReal contact-tail theorem and pinned toReal continuity at the finite endpoint.
-- source:
--   Proved 3240dd0b (original endpoint-cash ENNReal limit) plus pinned Mathlib ENNReal.tendsto_toReal. The explicit endpoint-finite premise is already supported by Proved c4e50d93 literal stopped Iic horizon integral finiteness. No loss of horizon mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_closed_contact_tail_toReal_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hFinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤) :
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
