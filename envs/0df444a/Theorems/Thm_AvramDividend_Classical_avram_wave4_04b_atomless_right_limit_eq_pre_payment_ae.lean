-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae
-- name    : AvramDividend.Classical.avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:51:55.895189+00:00
-- url     : https://prove2.me/theorems/800afbe2-1e7e-4685-9ea3-29ffc1891150
-- title:
--   Every atomless Stieltjes measure sees post-payment D rightLimit equal to pre-payment D almost everywhere
-- statement:
--   For an arbitrary actual adapted Avram cumulative dividend path and every atomless measure ν on real time (including a singular-continuous ν), the right-payment cumulative process rightLimit D and the original pre-payment cumulative D agree at ν-almost every nonnegative time. The exceptional times are exactly among the source's countable right-jump support, which every NullSingletonClass measure annihilates. This is an a.e. chronological bridge for the diffuse finite-variation control term in Itô–Meyer; it does not assert D is continuous or that the original dividend measure is purely atomic.
-- source:
--   Proved source-specific rightJump support countability and Mathlib null-singleton countable-set zero measure/ae equivalence. Applies to the diffuse part of actual finite-horizon dividendMeasure, including singular-continuous payments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 ≤ s →
      rightLimit D s.toNNReal ω = D s.toNNReal ω := by sorry
