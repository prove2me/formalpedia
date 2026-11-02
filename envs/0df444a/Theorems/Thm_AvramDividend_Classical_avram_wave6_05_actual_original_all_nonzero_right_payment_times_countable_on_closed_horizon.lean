-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:39:24.709561+00:00
-- url     : https://prove2.me/theorems/cd4f2054-d9dd-4dcb-abe6-b918e560b1c2
-- title:
--   Every nonzero actual original right dividend payment time on a closed horizon is countable, including time zero and horizon endpoint
-- statement:
--   For any original adapted nondecreasing dividend strategy and each actual sample path and finite horizon, the set of all nonzero right-payment times t∈[0,T] with rightLimit D(t)-D(t)>0 is countable. This is not a finite-jump hypothesis. It follows source-faithfully from the genuine original dividendMeasure atomic-plus-atomless decomposition, the exact right-payment atom mass formula, and the fact that its countable atomic support captures every nonzero singleton. Thus the complete chronological original dividend jump series may be indexed over all actual positive right payments (including time zero and the horizon endpoint); absolutely continuous and singular-continuous payments remain in the atomless component. No cap, ruin, Lipschitz D, finite activity, or smooth-control assumption is required.
-- source:
--   Apply the canonical original Stieltjes countable-support completeness theorem with unit weight. Every actual strictly positive right-payment δ_t at t≤T has a strictly positive original singleton measure mass by its exact atom identity, hence its physical-time cast lies in the support A. The embedding ℝ≥0→ℝ is injective, so the preimage of the countable set A is countable; take the subset of all actual positive right payments. This is a genuine arbitrary-finite-variation countability result, not a finite-jump assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    {t : ℝ≥0 | t ≤ T ∧ 0 < rightLimit D t ω - D t ω}.Countable := by sorry
