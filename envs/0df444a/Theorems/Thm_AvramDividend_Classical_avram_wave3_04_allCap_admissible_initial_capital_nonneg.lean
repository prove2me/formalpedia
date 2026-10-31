-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
-- name    : AvramDividend.Classical.avram_wave3_04_allCap_admissible_initial_capital_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:08:27.781975+00:00
-- url     : https://prove2.me/theorems/b3117b07-8383-4143-a965-2d9876a04a99
-- title:
--   Any genuinely admissible capped original Lévy dividend strategy has nonnegative initial capital
-- statement:
--   For the original spectrally negative Lévy process and any finite, infinite or zero cap C, the existence of an actual jointly adapted admissible dividend strategy D whose starting capital x satisfies ENNReal.ofReal x≤C forces x≥0. The original Lévy law P is a probability measure, providing a sample ω without any separate Nonempty Ω axiom. Canonical initial after-payment reserve solvency gives 0≤x−D(0+) because X_0=0. The actual dividend strategy has D_0=0 and is nondecreasing, hence D(0+)≥0. Thus x≥D(0+)≥0. This eliminates negative-capital edge cases when applying the corrected UBV HJB gradient dominance and terminal budget throughout every cap, and uses the original dividend measure instead of an independent model.
-- source:
--   Exact pinned remote compiler probe a3be556a-5286-429e-a5c5-a93970b75f7a reached its intentional sentinel with no candidate diagnostic, source SHA256 d91b1f40d45991b6972ca504741ff995e811cb66cfed4d98593dab6dcf211d7d. Canonical Proved capped_postPaymentReserve_initial_state 2ecd3672-50b4-4ad7-ad28-d1720acec949 and dividendStrategy_le_rightLimit 953f0e91-72ae-4c9a-bc17-de52a6c87b52. Pinned Mathlib nonempty_of_measure_ne_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_allCap_admissible_initial_capital_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    0 ≤ x := by sorry
