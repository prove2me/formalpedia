-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
-- name    : AvramDividend.Classical.avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:39:59.639668+00:00
-- url     : https://prove2.me/theorems/1a3528af-4aa0-4337-b8a4-12dabfe9325e
-- title:
--   Genuine reflected first-record discount lies strictly below one at every positive height
-- statement:
--   For any spectrally negative Lévy process admitting a strictly positive root φ of ψ(φ)=q, every positive first-record height b and every real reflected drawdown threshold a, the genuine discounted event E[e^{-qT_b};T_b<D_a] is strictly below one. Pathwise killed/unrestricted domination gives the upper bound exp(-φb)<1. No Standing, infinite-variation, scale function or excursion process enters the theorem.
-- source:
--   Proved exact original-process reflected kill ≤ unrestricted root transform 6a148bb3; strictly positive φ,b imply exp(-φb)<exp(0)=1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < b →
      (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P).toReal < 1 := by sorry
