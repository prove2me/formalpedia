-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_controlled_jump_support_exact
-- name    : AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_support_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:09:16.04534+00:00
-- url     : https://prove2.me/theorems/c06e9bd5-06f1-48be-81f5-57c4bb533516
-- title:
--   Exact original controlled post-payment reserve jump support is the union of Lévy and dividend jump supports
-- statement:
--   At every positive source time and for every sample path of the genuine spectrally negative Lévy process under any actual admissible nondecreasing dividend strategy, the post-payment controlled surplus U⁺_t has a jump relative to its strict-left limit if and only if either the original Lévy process jumps or a right dividend payment occurs. Negative source jumps and nonnegative dividend payments cannot cancel; proof uses the canonically Proved original source negative jump-mark sign, dividend rightLimit monotonicity and exact left-limit reserve identity. This provides exact source jump support for the stopped Itô–Meyer marked-jump decomposition, stronger than just countability, valid for both BV and UBV.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) controlled source jump mechanism; accepted actual source jump sign e95fe5bc, dividend monotonicity and original reserve left limit 06dc12b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_support_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (x + X.X t ω - rightLimit D t ω ≠
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ↔
      (X.X t ω ≠ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∨
        rightLimit D t ω ≠ D t ω) := by sorry
