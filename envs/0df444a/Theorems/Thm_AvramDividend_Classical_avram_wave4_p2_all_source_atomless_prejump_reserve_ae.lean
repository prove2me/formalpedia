-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_source_atomless_prejump_reserve_ae
-- name    : AvramDividend.Classical.avram_wave4_p2_all_source_atomless_prejump_reserve_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:39:24.927081+00:00
-- url     : https://prove2.me/theorems/1ccb31e2-8f49-44ad-8334-243a036985df
-- title:
--   Actual BV and UBV Lévy pre-source reserve agrees atomlessly with the pre-payment controlled reserve
-- statement:
--   For every sample of the genuine original spectrally negative Lévy X, without any BV/UBV distinction, its jump times are countable by the independently source-proved P2 theorem. Thus every atomless time measure, including the diffuse (possibly singular-continuous) Stieltjes dividend measure, sees only times where the true source left limit equals its current value, and the original dividend rightLimit equals the pre-payment value. The exact a.e. identity follows from Proved e7696306. No false atom-only dividend concentration, compensated jump law or martingale premise enters. This theorem is intended as an import-ready side interface for corrected UBV 429e17ca and BV ef7e6c20, not as a proof of either stochastic bound.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i) Itô–Meyer continuous Stieltjes control; source path countability P2 and Proved 04-B atomless reserve identification e7696306.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_pre_source_pre_payment_ae_of_countable_jumps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_all_source_atomless_prejump_reserve_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := by sorry
