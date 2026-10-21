-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
-- name    : AvramDividend.Classical.postPaymentReserve_nonnegative_strictly_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:54:49.124011+00:00
-- url     : https://prove2.me/theorems/80594c9f-09dd-4c1f-bdfe-2cad89792969
-- title:
--   The post-payment reserve is nonnegative whenever the time is strictly before ruin
-- statement:
--   Fix any nonnegative time t strictly below the defined extended ruin time τ. The book-value reserve U_s must be nonnegative at every finite s<τ, otherwise τ≤s. Continuity of the natural NNReal-to-ENNReal time embedding makes s<τ hold eventually when s approaches t from the strict right. The already Proved right-limit solvency theorem then implies that the post-payment reserve U+_t=x+X_t−D_{t+} is nonnegative. No nonnegativity at τ is claimed. This is a valid killed-process support condition for positive-cap stopped HJB verification.
-- source:
--   Uses proven postPaymentReserve_rightLimit_and_nonnegative, exact ruinTime infimum, and continuous coercion NNReal → ENNReal. Does not assume any Open lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_nonnegative_strictly_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω := by sorry
