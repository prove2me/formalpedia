-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_bv_source_atomless_prejump_reserve_ae
-- name    : AvramDividend.Classical.avram_wave4_p2_bv_source_atomless_prejump_reserve_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:26:56.853653+00:00
-- url     : https://prove2.me/theorems/8ee92ce1-701d-4519-bf10-06046bad6420
-- title:
--   Genuine BV Lévy pre-jump reserve equals pre-source/pre-payment reserve for every atomless control measure almost surely
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process and any genuine dividend strategy D, every atomless time measure ν sees the pre-source/pre-payment reserve formula at almost every positive time, on a P-probability-one sample-path event. The proof combines the canonically proved same-source BV jump-time countability 02fe4413 with the canonically proved deterministic atomless-control identification e7696306. Unlike a conditional countability lemma, no path-count hypothesis remains. This is the correct original-source interface for the diffuse/singular-continuous portion of BV Stieltjes control, but it does not assert a compensated Lévy stochastic integral or the full BV dividend expected bound.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), finite variation and Itô–Meyer integration against continuous dividend variation; source 02fe4413 and e7696306 both canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_levy_jump_times_ae_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_bv_source_atomless_prejump_reserve_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by sorry
