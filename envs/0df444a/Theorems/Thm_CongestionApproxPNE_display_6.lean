-- Prove2me | Theorems.Thm_CongestionApproxPNE_display_6
-- name    : CongestionApproxPNE.display_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:26.69607+00:00
-- url     : https://prove2.me/theorems/2df86cb5-a569-4586-989a-7917f0a22dd8
-- title:
--   Display (6) — $(1+w)^k+\beta w^d\ge 1$
-- statement:
--   For an integer $d$, take the parameter choice of the proof of Theorem 1: $w=\frac{\ln d}{2d}$, $k=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$, $\beta=\frac{1}{d^{k/(2(k+1))}(1+w)^d}$, $n=\left\lfloor\frac{1}{d^{1/(2(k+1))}w}\right\rfloor$.
--   For every integer $d\ge 4$,
--
--   $$
--   (1+w)^k+\beta w^d\ \ge\ 1. \tag{6}
--   $$
--
--   This bounds below the numerator of the second ratio of (3) at the parameter choice.
--
--   Differences from the source:
--   - encoding: ⌈·⌉ and ⌊·⌋ of reals; d^{k/(2(k+1))} etc. → Nat.ceil, Nat.floor, Real.rpow; reason: the arguments are nonnegative for d ≥ 4, where Nat.ceil/Nat.floor equal the integer ceiling/floor; Real.rpow is the real power of d > 0
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, display (6), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **Display (6): the numerator of the second ratio is at least `1`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, display (6), p.6: "(1 + w)^k + βw^d ≥ 1;".

For every integer `d ≥ 4`, at the parameter choice: `(1+w)^k + βw^d ≥ 1`.

**Formalization Note** `k = kd d`, `w = wChoice d`, `β = betaChoice d`, `n = nChoice d` are the
paper's choice `w = ln d/(2d)`, `k = ⌈ln d/(2 ln ln d)⌉`, `β = 1/(d^{k/(2(k+1))}(1+w)^d)`,
`n = ⌊1/(d^{1/(2(k+1))} w)⌋` (p.6). `d ≥ 4` is the range for which the paper states the choice is
admissible ("for d ≥ 4"). `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem display_6 (d : ℕ) (hd : 4 ≤ d) :
    1 ≤ (1 + wChoice d) ^ kd d + betaChoice d * wChoice d ^ d := by sorry

end CongestionApproxPNE
