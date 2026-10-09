-- Prove2me | Theorems.Thm_ExploreFirst_Absolute_kl_monotone_right
-- name    : ExploreFirst.Absolute.kl_monotone_right
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:15.547976+00:00
-- url     : https://prove2.me/theorems/82d199c3-55fb-41e3-aa5f-09c9d5d5f29d
-- title:
--   Monotonicity of Bernoulli divergence in its second parameter
-- statement:
--   Fix $0\le p\le q\le q'\le1$. Bernoulli divergence is nondecreasing in its second parameter to the right of $p$:
--   $$\mathrm{kl}(p,q)\le\mathrm{kl}(p,q').$$
--
--   This is the monotonicity statement used on page 11 to replace the alternative problem's expected arm fraction by $1/K$. The boundary value $q'=1$ is included.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 11, proof of Theorem 2, monotonicity sentence

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

namespace ExploreFirst.Absolute

/-- Monotonicity used in the proof of Theorem 2, p. 11. -/
theorem kl_monotone_right (p q q' : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hqq' : q ≤ q') (hq' : q' ≤ 1) :
    ExploreFirst.FundIneq.klBer p q ≤ ExploreFirst.FundIneq.klBer p q' := by sorry

end ExploreFirst.Absolute
