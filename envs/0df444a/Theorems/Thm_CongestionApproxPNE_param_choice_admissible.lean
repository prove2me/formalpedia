-- Prove2me | Theorems.Thm_CongestionApproxPNE_param_choice_admissible
-- name    : CongestionApproxPNE.param_choice_admissible
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:27.423062+00:00
-- url     : https://prove2.me/theorems/a0832894-07c3-4c5c-97dd-3c67e24388de
-- title:
--   Proof of Theorem 1, p.6 — the parameter choice satisfies $k\in\{1,\dots,d\}$ and $w,\beta\in[0,1]$ for $d\ge 4$
-- statement:
--   For an integer $d$, take the parameter choice of the proof of Theorem 1: $w=\frac{\ln d}{2d}$, $k=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$, $\beta=\frac{1}{d^{k/(2(k+1))}(1+w)^d}$, $n=\left\lfloor\frac{1}{d^{1/(2(k+1))}w}\right\rfloor$.
--   For every integer $d\ge 4$,
--
--   $$
--   k\in\{1,\dots,d\},\qquad w\in[0,1],\qquad \beta\in[0,1].
--   $$
--
--   So the choice is a point of the family over which (3) is taken.
--
--   Differences from the source:
--   - encoding: ⌈·⌉ and ⌊·⌋ of reals; d^{k/(2(k+1))} etc. → Nat.ceil, Nat.floor, Real.rpow; reason: the arguments are nonnegative for d ≥ 4, where Nat.ceil/Nat.floor equal the integer ceiling/floor; Real.rpow is the real power of d > 0
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), "One can check that this choice satisfies k ∈ {1, . . . , d} (for d ≥ 4) and w, β ∈ [0, 1]."

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The parameter choice is admissible.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, p.6: "we take the following choice of parameters: w = ln d/(2d),
k = ⌈ln d/(2 ln ln d)⌉, β = 1/(d^{k/(2(k+1))}(1 + w)^d), n = ⌊1/(d^{1/(2(k+1))} w)⌋. One can check
that this choice satisfies k ∈ {1, . . . , d} (for d ≥ 4) and w, β ∈ [0, 1]."

For every integer `d ≥ 4`: `1 ≤ k ≤ d`, `0 ≤ w ≤ 1` and `0 ≤ β ≤ 1`.

**Formalization Note** `k = kd d`, `w = wChoice d`, `β = betaChoice d`, `n = nChoice d` are the
paper's choice `w = ln d/(2d)`, `k = ⌈ln d/(2 ln ln d)⌉`, `β = 1/(d^{k/(2(k+1))}(1+w)^d)`,
`n = ⌊1/(d^{1/(2(k+1))} w)⌋` (p.6). `d ≥ 4` is the range for which the paper states the choice is
admissible ("for d ≥ 4"). `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem param_choice_admissible (d : ℕ) (hd : 4 ≤ d) :
    1 ≤ kd d ∧ kd d ≤ d ∧ 0 ≤ wChoice d ∧ wChoice d ≤ 1 ∧ 0 ≤ betaChoice d ∧ betaChoice d ≤ 1 := by sorry

end CongestionApproxPNE
