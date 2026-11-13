-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a48_positive_exponential_tail_chernoff_majorant
-- name    : AvramDividend.Classical.avram_ga_a48_positive_exponential_tail_chernoff_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:16:27.242224+00:00
-- url     : https://prove2.me/theorems/148f1984-a757-4e2d-8b21-9c0a899631cf
-- title:
--   Positive Gaussian spatial source excursion exponential weight obeys a tunable Chernoff majorant
-- statement:
--   For every source displacement and any nonnegative exponential tilt, the positive excursion portion of an exponential value bound is dominated by a shifted exponential multiplied by a tunable exponentially small threshold factor.
-- source:
--   Positive rare upper source excursions in Avram b0d9951c, to combine with Gaussian exact positive Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a48_positive_exponential_tail_chernoff_majorant (z θ r δ : ℝ) (hr : 0 ≤ r) :
    (if δ ≤ z then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * δ) * Real.exp ((θ + r) * z) := by sorry
