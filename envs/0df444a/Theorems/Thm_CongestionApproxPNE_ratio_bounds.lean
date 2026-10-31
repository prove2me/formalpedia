-- Prove2me | Theorems.Thm_CongestionApproxPNE_ratio_bounds
-- name    : CongestionApproxPNE.ratio_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:48.508145+00:00
-- url     : https://prove2.me/theorems/f57aa946-7bfa-4974-9511-c1457cd2fa63
-- title:
--   End of the proof of Theorem 1 — both ratios of (3) are at least $\sqrt d/(2\ln d)$ at the parameter choice
-- statement:
--   For an integer $d$, take the parameter choice of the proof of Theorem 1: $w=\frac{\ln d}{2d}$, $k=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$, $\beta=\frac{1}{d^{k/(2(k+1))}(1+w)^d}$, $n=\left\lfloor\frac{1}{d^{1/(2(k+1))}w}\right\rfloor$.
--   Then:
--
--   1. there is $d_0$ such that for every integer $d\ge d_0$,
--   $$
--   \frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta}\ \ge\ \frac{\sqrt d}{2\ln d};
--   $$
--   2. for every integer $d\ge 4$,
--   $$
--   \frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}\ \ge\ \frac{\sqrt d}{2\ln d}.
--   $$
--
--   The first bound combines (4), (5) and Lemma 3 (the right-hand side of (5) is eventually at most $4$); the second combines (6) and (7). Since the parameter choice is admissible, $\alpha(d)\ge\sqrt d/(2\ln d)$ for all large $d$.
--
--   Differences from the source:
--   - reading: the second ratio bounded "from (6) and (7)", with no "large d" → the second bound for every integer d ≥ 4; reason: (6) and (7) hold for every d ≥ 4, the range in which the choice is admissible; this is the stronger of the readings "eventually" and "for d ≥ 4"
--   - encoding: ⌈·⌉ and ⌊·⌋ of reals; d^{k/(2(k+1))} etc. → Nat.ceil, Nat.floor, Real.rpow; reason: the arguments are nonnegative for d ≥ 4, where Nat.ceil/Nat.floor equal the integer ceiling/floor; Real.rpow is the real power of d > 0
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), the two ratio bounds after display (7)

import Mathlib
import Definitions.Def_CongestionApproxPNE_ratioOne
import Definitions.Def_CongestionApproxPNE_ratioTwo
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **Both ratios of (3) are at least `√d/(2 ln d)` at the parameter choice.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, end of the proof of Theorem 1, p.6: "In the Appendix, we prove (Lemma 3) that the final
quantity in (5) converges to 1 as d → ∞; in particular, it is upper bounded by 4 for d large
enough … Thus, we can lower bound the ratios of (3) as (1 + nβ(1 + w)^d)/((1 + nw)^k + nβ) ≥
(2√d/ln d)/4 = √d/(2 ln d) … (from (4), (5) and large d); ((1 + w)^k + βw^d)/((nw)^k + β(1 + w)^d)
≥ 1/(2 ln d/√d) = √d/(2 ln d) … (from (6) and (7))."

1. There is `d₀` such that for every integer `d ≥ d₀`, at the parameter choice,
   `(1 + nβ(1+w)^d)/((1+nw)^k + nβ) ≥ √d/(2 ln d)`.
2. For every integer `d ≥ 4`, at the parameter choice,
   `((1+w)^k + βw^d)/((nw)^k + β(1+w)^d) ≥ √d/(2 ln d)`.

**Formalization Note** The first bound uses "large d" (through Lemma 3), the second only (6) and
(7), which hold for `d ≥ 4`; the two clauses keep that distinction. The paper's numerical remark
"d ≥ 8 suffices" is not part of the statement. Parameters as in `param_choice_admissible`. -/
theorem ratio_bounds :
    (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Real.sqrt d / (2 * Real.log d) ≤
        ratioOne d (nChoice d) (kd d) (wChoice d) (betaChoice d)) ∧
    (∀ d : ℕ, 4 ≤ d →
      Real.sqrt d / (2 * Real.log d) ≤
        ratioTwo d (nChoice d) (kd d) (wChoice d) (betaChoice d)) := by sorry

end CongestionApproxPNE
