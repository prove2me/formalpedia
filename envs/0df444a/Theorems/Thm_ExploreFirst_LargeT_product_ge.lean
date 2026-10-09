-- Prove2me | Theorems.Thm_ExploreFirst_LargeT_product_ge
-- name    : ExploreFirst.LargeT.product_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:19.638799+00:00
-- url     : https://prove2.me/theorems/4790fadc-c012-497e-8897-f569f1450ed9
-- title:
--   p. 17 — three-factor product inequality
-- statement:
--   For any three real numbers $a,b,c\in[0,1]$,
--   $$
--   (1-a)(1-b)(1-c)\ge1-(a+b+c).
--   $$
--   The product bound is the elementary step used to collect the three explicit error terms in Theorem 5. Its nonnegativity conditions also specify the range needed for the paper's use of this step.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 17, sentence before Theorem 5

import Mathlib

namespace ExploreFirst.LargeT

/-- The three-factor inequality quoted immediately before Theorem 5. -/
theorem product_ge (a b c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 - (a + b + c) ≤ (1 - a) * (1 - b) * (1 - c) := by sorry

end ExploreFirst.LargeT
