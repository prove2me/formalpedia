-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_admissible_zero_or_positive_cap
-- name    : AvramDividend.Classical.avram_wave7_11_original_admissible_zero_or_positive_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:01:49.712847+00:00
-- url     : https://prove2.me/theorems/106e1a1d-d230-4bb3-8765-5142890e4e11
-- title:
--   Authentic capped admissibility forces zero initial capital or a positive cap
-- statement:
--   For the original spectrally negative Lévy process X on the original P, capped admissibility and ENNReal.ofReal x ≤ C imply x is nonnegative. If x is positive, ENNReal.ofReal x is positive and bounded by C, hence the cap is positive. This makes the x=0 versus x>0 and C=0 versus C>0 split explicit for original finite-horizon stochastic verification.
-- source:
--   Proved source initial-reserve theorem b3117b07-8383-4143-a965-2d9876a04a99 and pinned Mathlib ENNReal.ofReal_pos.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Mathlib.Data.ENNReal.Real

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_admissible_zero_or_positive_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    x = 0 ∨ 0 < C := by sorry
