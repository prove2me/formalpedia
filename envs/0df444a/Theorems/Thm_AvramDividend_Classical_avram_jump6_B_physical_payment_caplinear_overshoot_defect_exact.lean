-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
-- name    : AvramDividend.Classical.avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:28:53.829191+00:00
-- url     : https://prove2.me/theorems/5eab0b6b-160c-4731-8918-6e115019f337
-- title:
--   Exact original-grid payment signed-budget decomposition into caplinear budget and previsible overshoot defect
-- statement:
--   For physical-grid payment times, whenever the caplinear extension V equals the original HJB candidate w at initial and every postpayment reserve, the original signed w payment residual equals the caplinear signed V budget plus the exact sum of weighted previsible overshoot defects V(Z)-w(Z). This finite algebra isolates the only remaining previsible finite-cap correction after the original source all-cap caplinear Stieltjes cash budget. The original-process postpayment equality is independently Proved for admissible dividends and can instantiate these hypotheses.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_weighted_signed_potential_drop_sum_swap
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
    {ι : Type*} (s : Finset ι)
    (E : ι → ℝ) (pre post : ι → ℝ) (w V : ℝ → ℝ)
    (initial final : ℝ)
    (hInit : V initial = w initial)
    (hFinal : V final = w final)
    (hPost : ∀ i ∈ s, V (post i) = w (post i)) :
    (w initial - w final) +
      (∑ i ∈ s, E i * (w (post i) - w (pre i))) =
    (V initial - V final) -
      (∑ i ∈ s, E i * (V (pre i) - V (post i))) +
      (∑ i ∈ s, E i * (V (pre i) - w (pre i))) := by sorry
