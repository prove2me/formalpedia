-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_discounted_increment_decomposition
-- name    : AvramDividend.Classical.postPaymentReserve_discounted_increment_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:31:13.480702+00:00
-- url     : https://prove2.me/theorems/983c337d-b416-45b5-8026-7f828b5bc0f9
-- title:
--   Discounted post-payment reserve increments obey the exact product decomposition
-- statement:
--   The discounted difference of a càdlàg post-payment reserve at any two nonnegative times decomposes into the discounted Lévy increment less the full right-limit dividend increment, and the discount-factor change times the initial reserve at the earlier time. The identity is pathwise and holds without stochastic regularity or integrability assumptions.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_discounted_increment_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    Real.exp (-(q * (t : ℝ))) *
      (x + X.X t ω - rightLimit D t ω) -
    Real.exp (-(q * (s : ℝ))) *
      (x + X.X s ω - rightLimit D s ω) =
    Real.exp (-(q * (t : ℝ))) *
      ((X.X t ω - X.X s ω) -
        (rightLimit D t ω - rightLimit D s ω)) +
    (Real.exp (-(q * (t : ℝ))) -
       Real.exp (-(q * (s : ℝ)))) *
      (x + X.X s ω - rightLimit D s ω) := by sorry
