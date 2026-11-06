-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_positive_reserve_suffices_all_cap_and_top
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_positive_reserve_suffices_all_cap_and_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:04:50.377203+00:00
-- url     : https://prove2.me/theorems/340788ec-f4fd-4ee6-9bde-a202bb244096
-- title:
--   Original UBV verification of strictly positive starting reserves implies all capped and unrestricted reserves
-- statement:
--   Original source-exact UBV positive-reserve reduction for local
--   verification. If the capped verification candidate upper-bounds
--   valueFunctionLe for every strictly positive admissible starting reserve,
--   the already-Proved instant-ruin zero-reserve uniform-cap certificate
--   fills x=0. At cap top, the exact original cap-top equality yields the
--   unrestricted upper bound. No extra martingale, ruin atom, HJB, smoothness
--   or equality-in-law premise is introduced.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_uniform_all_caps
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_positive_reserve_suffices_all_cap_and_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0) (C : ℝ≥0∞)
    (hPositive : ∀ x : ℝ, 0 < x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
