-- Prove2me | Theorems.Thm_CongestionApproxPNE_display_4
-- name    : CongestionApproxPNE.display_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:31.281276+00:00
-- url     : https://prove2.me/theorems/ad99350b-50ea-4067-aaa8-63045bd95620
-- title:
--   Display (4) — $1+n\beta(1+w)^d\ge 2\sqrt d/\ln d$
-- statement:
--   For an integer $d$, take the parameter choice of the proof of Theorem 1: $w=\frac{\ln d}{2d}$, $k=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$, $\beta=\frac{1}{d^{k/(2(k+1))}(1+w)^d}$, $n=\left\lfloor\frac{1}{d^{1/(2(k+1))}w}\right\rfloor$.
--   For every integer $d\ge 4$,
--
--   $$
--   1+n\beta(1+w)^d\ \ge\ \frac{2\sqrt d}{\ln d}. \tag{4}
--   $$
--
--   This bounds below the numerator of the first ratio of (3) at the parameter choice.
--
--   Differences from the source:
--   - encoding: ⌈·⌉ and ⌊·⌋ of reals; d^{k/(2(k+1))} etc. → Nat.ceil, Nat.floor, Real.rpow; reason: the arguments are nonnegative for d ≥ 4, where Nat.ceil/Nat.floor equal the integer ceiling/floor; Real.rpow is the real power of d > 0
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, display (4), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **Display (4): the numerator of the first ratio is at least `2√d/ln d`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, display (4), p.6: "1 + nβ(1 + w)^d ≥ … ≥ 2d/(d^{1/2} ln d) (since
d ≥ 1) = 2√d/ln d".

For every integer `d ≥ 4`, at the parameter choice: `1 + nβ(1+w)^d ≥ 2√d / ln d`.

**Formalization Note** `k = kd d`, `w = wChoice d`, `β = betaChoice d`, `n = nChoice d` are the
paper's choice `w = ln d/(2d)`, `k = ⌈ln d/(2 ln ln d)⌉`, `β = 1/(d^{k/(2(k+1))}(1+w)^d)`,
`n = ⌊1/(d^{1/(2(k+1))} w)⌋` (p.6). `d ≥ 4` is the range for which the paper states the choice is
admissible ("for d ≥ 4"). `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem display_4 (d : ℕ) (hd : 4 ≤ d) :
    2 * Real.sqrt d / Real.log d ≤
      1 + (nChoice d : ℝ) * betaChoice d * (1 + wChoice d) ^ d := by sorry

end CongestionApproxPNE
