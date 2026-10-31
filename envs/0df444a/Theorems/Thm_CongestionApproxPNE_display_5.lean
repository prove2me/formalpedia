-- Prove2me | Theorems.Thm_CongestionApproxPNE_display_5
-- name    : CongestionApproxPNE.display_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:22.643626+00:00
-- url     : https://prove2.me/theorems/16ceeae1-ae4f-48ec-8ebf-fbc223ede477
-- title:
--   Display (5) — $(1+nw)^k+n\beta\le(1+d^{-1/(2(k+1))})^k+2\sqrt d/(\ln d\,(1+\ln d/(2d))^d)$
-- statement:
--   For an integer $d$, take the parameter choice of the proof of Theorem 1: $w=\frac{\ln d}{2d}$, $k=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$, $\beta=\frac{1}{d^{k/(2(k+1))}(1+w)^d}$, $n=\left\lfloor\frac{1}{d^{1/(2(k+1))}w}\right\rfloor$.
--   For every integer $d\ge 4$,
--
--   $$
--   (1+nw)^k+n\beta\ \le\ \left(1+d^{-\frac{1}{2(k+1)}}\right)^k+\frac{2\sqrt d}{\ln d\left(1+\frac{\ln d}{2d}\right)^d}. \tag{5}
--   $$
--
--   The right-hand side is the sequence $g(d)$ of Lemma 3, which tends to $1$; so the denominator of the first ratio of (3) stays bounded.
--
--   Differences from the source:
--   - encoding: ⌈·⌉ and ⌊·⌋ of reals; d^{k/(2(k+1))} etc. → Nat.ceil, Nat.floor, Real.rpow; reason: the arguments are nonnegative for d ≥ 4, where Nat.ceil/Nat.floor equal the integer ceiling/floor; Real.rpow is the real power of d > 0
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, display (5), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **Display (5): the denominator of the first ratio is at most `g(d)`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, display (5), p.6: "(1 + nw)^k + nβ ≤ … = (1 + d^{−1/(2(k+1))})^k +
2√d/(ln d (1 + ln d/(2d))^d)".

For every integer `d ≥ 4`, at the parameter choice:
`(1 + nw)^k + nβ ≤ (1 + d^{−1/(2(k+1))})^k + 2√d / (ln d · (1 + ln d/(2d))^d)`.

**Formalization Note** `k = kd d`, `w = wChoice d`, `β = betaChoice d`, `n = nChoice d` are the
paper's choice `w = ln d/(2d)`, `k = ⌈ln d/(2 ln ln d)⌉`, `β = 1/(d^{k/(2(k+1))}(1+w)^d)`,
`n = ⌊1/(d^{1/(2(k+1))} w)⌋` (p.6). `d ≥ 4` is the range for which the paper states the choice is
admissible ("for d ≥ 4"). `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem display_5 (d : ℕ) (hd : 4 ≤ d) :
    (1 + (nChoice d : ℝ) * wChoice d) ^ kd d + (nChoice d : ℝ) * betaChoice d ≤
      (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d +
        2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d) := by sorry

end CongestionApproxPNE
