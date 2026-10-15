-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_lemma_25
-- name    : AdvanceSales.Pricing.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:57.324596+00:00
-- url     : https://prove2.me/theorems/dd897cf4-ba8b-4e52-af3d-4c3d0e69e560
-- title:
--   Lemma 25 — strict convexity and the two roots of the switching function
-- statement:
--   For $k>0$, the switching function
--
--   $$f_k(v)=\left(1-\frac{v}{k+1}\right)W-\ln(v-k),\qquad v>k,$$
--
--   is strictly convex on its domain. It has exactly two roots there: the smaller is $k+1$, and the other is larger than $k+1$.
--
--   This identifies the second root used as the threshold $v_f$ in Theorem 4.
--
--   **Formalization Note** The proof's word “concave” is a slip; the lemma and its positive second derivative say “convex.” The domain $v>k$ makes the logarithm meaningful.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, p. 42, Lemma 25 and Definition 24

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem lemma_25 (k : ℝ) (hk : 0 < k) :
    StrictConvexOn ℝ (Set.Ioi k) (f k) ∧
      ∃ w : ℝ, k + 1 < w ∧
        {v : ℝ | k < v ∧ f k v = 0} = {k + 1, w} := by sorry

end AdvanceSales.Pricing
