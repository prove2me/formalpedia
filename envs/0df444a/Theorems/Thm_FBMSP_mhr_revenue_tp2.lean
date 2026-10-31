-- Prove2me | Theorems.Thm_FBMSP_mhr_revenue_tp2
-- name    : FBMSP.mhr_revenue_tp2
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:54:53.721153+00:00
-- url     : https://prove2.me/theorems/fe2bcf95-66da-4eb4-acdb-7b32fcb98d02
-- title:
--   Lemma 2(b), analytic step — Revenue TP2 inequality
-- statement:
--   For an integrable mean-zero MHR error law, any real $x_1\le x_2$, and $0\le p_1\le p_2$, the common location-family revenue satisfies
--   $$r(x_1,p_2)r(x_2,p_1)\le r(x_1,p_1)r(x_2,p_2).$$
--   This is the source's PF2 argument written without division. It retains zero prices, zero sale probabilities, ties, and bounded-support error distributions.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Proof of Lemma 2(b), pp.42–43 (ec8–ec9).

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Division-free TP2 inequality used in the proof of Lemma 2(b).  It includes
zero sale probabilities, zero prices, and ties.  Draft statement; proof open. -/
theorem mhr_revenue_tp2 (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (x₁ x₂ p₁ p₂ : ℝ) (hx : x₁ ≤ x₂)
    (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p₂) :
    postedRevenue η x₁ p₂ * postedRevenue η x₂ p₁ ≤
      postedRevenue η x₁ p₁ * postedRevenue η x₂ p₂ := by sorry

end FBMSP
