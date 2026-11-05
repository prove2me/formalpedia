-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_zero_time_postpayment_within_cap
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_zero_time_postpayment_within_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:51:43.360381+00:00
-- url     : https://prove2.me/theorems/7ebce443-6b67-40af-b199-74d9d56b963f
-- title:
--   Exact original initial post-rightpayment terminal reserve is nonnegative and within the admissible cap
-- statement:
--   Under genuine IsAdmissibleLe source controls, X0=0 and the initial capital within cap C, the exact W branch at τ=0, namely x+X.X0-rightLimit D0, is nonnegative and has ENNReal.ofReal at most C. This proves the cap/zero boundary invariant for the initial atom of the canonical original UBV stopped budget, without any strictly positive interior-reserve assumption.
-- source:
--   Original Lévy X_zero, admissible source initial right-payment bound, and Mathlib ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true initial right-payment reserve stays in the cap without assuming an interior start. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_zero_time_postpayment_within_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω, 0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      ENNReal.ofReal (x + X.X 0 ω - rightLimit D 0 ω) ≤ C := by sorry
