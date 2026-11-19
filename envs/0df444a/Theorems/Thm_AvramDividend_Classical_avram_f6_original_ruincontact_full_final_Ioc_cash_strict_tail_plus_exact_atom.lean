-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
-- name    : AvramDividend.Classical.avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:49:55.166756+00:00
-- url     : https://prove2.me/theorems/efee280a-4261-45b6-87df-109e78f9c550
-- title:
--   Original full final Ioc ruin-contact cash splits into strict last-cell tail and terminal dividend atom
-- statement:
--   For any genuine Lévy process X, original dividend process D, realised finite contact clock T and positive physical canonical mesh width n/(j+1), the discounted Stieltjes cash restricted to original paymentTimes and the closed-right last interval (T−width,T] equals exactly the strict-pre-T cash on (T−width,T) plus the discounted original paymentTimes cash concentrated at singleton {T}. The equality is valid in ENNReal without finiteness assumptions and retains any actual terminal dividend atom instead of incorrectly discarding it. It provides a physically exact bridge between the proven strict cash tail limit and the inclusive F6 stopped terminal Iic cash.
-- source:
--   Proved original paymentTimes measurableSet a3a9dc89; pinned Mathlib lintegral_union for disjoint measurable last interval and terminal singleton.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_ruincontact_full_final_Ioc_cash_strict_tail_plus_exact_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (q : ℝ) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
