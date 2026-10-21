-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
-- name    : AvramDividend.Classical.capped_postPaymentReserve_within_cap_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:21:32.659376+00:00
-- url     : https://prove2.me/theorems/a8120e3c-049c-465c-9ad2-bbf91f9b20a1
-- title:
--   Before ruin, the after-payment reserve of a capped strategy lies between zero and the cap
-- statement:
--   For every nonnegative time t>0 strictly before ruin of a capped-admissible dividend strategy, the post-payment reserve U_t+=x+X_t−D_{t+} is nonnegative and its ENNReal.ofReal is at most the cap C. The lower inequality follows from the separately Proved right-limit/ruin-time bridge. For the upper inequality, IsAdmissibleLe bounds the book-value reserve U_t at t>0, and the Proved atom decomposition implies U_t+≤U_t, so ENNReal.ofReal_mono transports the cap bound. This is the proper HJB state-domain interface that respects right dividend atoms and the formal strict ruin time; it does not assume the stochastic Ito budget.
-- source:
--   Depends on Proved postPaymentReserve_rightJump_decomposition and, once accepted, Proved postPaymentReserve_nonnegative_strictly_before_ruin. Do not publish while latter is Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_postPaymentReserve_within_cap_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by sorry
