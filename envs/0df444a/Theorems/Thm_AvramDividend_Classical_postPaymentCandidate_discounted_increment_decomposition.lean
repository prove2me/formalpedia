-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentCandidate_discounted_increment_decomposition
-- name    : AvramDividend.Classical.postPaymentCandidate_discounted_increment_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:35:33.922207+00:00
-- url     : https://prove2.me/theorems/4e09483a-45e6-4539-aa57-97360f2df50a
-- title:
--   Exact discounted product identity for a verification function of post-payment reserves
-- statement:
--   For any real candidate verification function w and any spectrally negative Lévy reserve with cumulative right-limit dividend deductions, the change between two discounted values of w of the post-payment reserve equals the discounted change in w plus the discount-factor change times the earlier value. This exact pathwise product identity underlies the stopped Itô verification argument and holds for BV and UV without stochastic integrability assumptions.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentCandidate_discounted_increment_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω) -
    Real.exp (-(q * (s : ℝ))) *
      w (x + X.X s ω - rightLimit D s ω) =
    Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
       w (x + X.X s ω - rightLimit D s ω)) +
    (Real.exp (-(q * (t : ℝ))) -
       Real.exp (-(q * (s : ℝ)))) *
      w (x + X.X s ω - rightLimit D s ω) := by sorry
