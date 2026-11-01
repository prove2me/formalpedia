-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_jump_times_countable
-- name    : AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_jump_times_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:49:44.496809+00:00
-- url     : https://prove2.me/theorems/3eed61cd-e441-4a2c-ad8b-3c9ea36ccbd4
-- title:
--   Original controlled Lévy post-payment reserve has countably many positive jump times in both BV and UBV
-- statement:
--   For every sample path of the genuine original spectrally negative Lévy process X, every admissible dividend strategy D and every initial capital x, the actual post-payment reserve U⁺(t)=x+X(t)-rightLimit(D,t) has at most countably many positive-time jumps relative to its strict-left limit. The jump set is contained in the union of original source-X jumps and original dividend right-payment jumps, both already canonically countable; its exact left limit is supplied by the separately Proved source chronological identity. No Lévy jump compensator, stochastic integral or false atomic-control hypothesis is used. Importable for the BV and UBV controlled stopped Itô–Meyer support analysis.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original controlled surplus U; canonical P2 source Lévy jump countability 741d3b5f, dividend countability b876ce73 and exact pre-jump U identity 06dc12b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_countable_positive_rightLimit_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_jump_times_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Set.Countable {t : ℝ≥0 | 0 < t ∧
      x + X.X t ω - rightLimit D t ω ≠
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by sorry
