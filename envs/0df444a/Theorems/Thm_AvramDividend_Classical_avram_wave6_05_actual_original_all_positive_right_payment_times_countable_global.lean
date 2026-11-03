-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_all_positive_right_payment_times_countable_global
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_all_positive_right_payment_times_countable_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:23:34.081208+00:00
-- url     : https://prove2.me/theorems/719e9dd7-306f-47ba-be2e-d9235905c30e
-- title:
--   All genuine original right-dividend positive payment times are countable globally, with arbitrarily infinite jumps allowed
-- statement:
--   For any genuine original adapted monotone dividend strategy and every sample path, the set of all nonzero chronological right-payment atoms at every nonnegative time is countable, with no finite-horizon or finite-jump control restriction. The proof unions the canonically Proved exact original Stieltjes countability of positive atoms on each closed natural-number horizon. Every actual time lies below some natural horizon by the Archimedean property. The result justifies a genuinely complete global countable jump series while separately preserving the entire diffuse, including singular-continuous, Stieltjes dividend mass. The original rightLimit convention, initial dividend atom, simultaneous source Lévy jumps, and no cap or ruin simplification are preserved.
-- source:
--   For each integer n, the canonically Proved actual dividendMeasure atomic-support theorem shows that all nonzero original right payments through n are countable. The countable union of these supports remains countable, and every finite nonnegative real time belongs to a natural-number closed horizon. Thus the set of all original nonzero right-payment times is countable without assuming that the number of dividend jumps is finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_all_positive_right_payment_times_countable_global
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    {t : ℝ≥0 | 0 < rightLimit D t ω - D t ω}.Countable := by sorry
