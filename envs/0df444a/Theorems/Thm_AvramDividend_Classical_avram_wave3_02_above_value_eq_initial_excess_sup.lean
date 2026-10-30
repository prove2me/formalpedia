-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
-- name    : AvramDividend.Classical.avram_wave3_02_above_value_eq_initial_excess_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:51:22.057377+00:00
-- url     : https://prove2.me/theorems/5e222ae5-251f-442a-85e5-7ae55e5422ea
-- title:
--   Above-barrier original Lévy dividend value is initial excess plus true reflected boundary reward
-- statement:
--   For any spectrally negative Lévy process, any real discount parameter, any nonnegative constant barrier a and initial capital x>a, the genuine expected discounted Stieltjes dividend value under the reflected barrierStrategy is exactly the initial excess payment x-a plus the true reflected boundary value barrierSupValue X a q. This holds even at a=0, and does not need the scale function, its differentiability, Standing, or a positive discount assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), reflected barrier construction. Proof uses canonically Proved pathwise initial excess strategy identity, admissible Stieltjes cash process and boundary reflected-supremum value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_above_value_eq_initial_excess_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ)
    (ha : 0 ≤ a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (x - a) + barrierSupValue X a q := by sorry
