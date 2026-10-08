-- Prove2me | Theorems.Thm_DGPNash_NashMap_lemma_3_6
-- name    : DGPNash.NashMap.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:37:03.586449+00:00
-- url     : https://prove2.me/theorems/79187767-6cc8-4da5-ab8a-df349f549c86
-- title:
--   Lemma 3.6 — normalized-sum inequality
-- statement:
--   Let $x,x',y,y',z,z'$ be nonnegative real numbers and suppose $(x+y)/(1+z)\le1$. Then
--
--   $$\left|\frac{x+y}{1+z}-\frac{x'+y'}{1+z'}\right|\le |x-x'|+|y-y'|+|z-z'|.$$
--
--   This elementary inequality controls how a normalized coordinate changes when its numerator and denominator change; it is used in the paper's Lipschitz bound for Nash's map.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 206, Lemma 3.6; https://doi.org/10.1137/070699652

import Mathlib

namespace DGPNash.NashMap

/-- Lemma 3.6, p. 206. -/
theorem lemma_3_6 (x x' y y' z z' : ℝ)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hfrac : (x + y) / (1 + z) ≤ 1) :
    |(x + y) / (1 + z) - (x' + y') / (1 + z')| ≤
      |x - x'| + |y - y'| + |z - z'| := by sorry

end DGPNash.NashMap
