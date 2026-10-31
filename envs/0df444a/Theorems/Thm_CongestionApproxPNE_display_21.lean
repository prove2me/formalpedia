-- Prove2me | Theorems.Thm_CongestionApproxPNE_display_21
-- name    : CongestionApproxPNE.display_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:55.078601+00:00
-- url     : https://prove2.me/theorems/f9a7e95d-8957-4be4-a788-b074cd58c436
-- title:
--   Display (21) — $\exp(xy/(x+y))<(1+x/y)^y<\exp(x)$ for $x,y>0$
-- statement:
--   For all real $x,y>0$,
--
--   $$
--   \exp\left(\frac{xy}{x+y}\right)\ <\ \left(1+\frac{x}{y}\right)^{y}\ <\ \exp(x). \tag{21}
--   $$
--
--   The paper cites this pair of inequalities (NIST Handbook of Mathematical Functions, Eq. 4.5.13) and uses them to bound both halves of the sequence $g(d)$ in Lemma 3.
--
--   **Formalization Note** The exponent $y$ is real, so $(1+x/y)^y$ is the real power `Real.rpow` of a positive base.
--
--   Differences from the source: none.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, display (21), p.23 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **Display (21): `exp(xy/(x+y)) < (1 + x/y)^y < exp(x)` for all `x, y > 0`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, display (21), p.23: "exp(xy/(x + y)) < (1 + x/y)^y < exp(x),
for all x, y > 0." (cited there from the NIST Handbook, Eq. 4.5.13).

**Formalization Note** `y` is real, so `(1 + x/y)^y` is `Real.rpow` (its base is positive). -/
theorem display_21 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (x * y / (x + y)) < (1 + x / y) ^ y ∧ (1 + x / y) ^ y < Real.exp x := by sorry

end CongestionApproxPNE
