-- Prove2me | Theorems.Thm_CongestionApproxPNE_lemma_3
-- name    : CongestionApproxPNE.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:04.548417+00:00
-- url     : https://prove2.me/theorems/d4e6859b-dbfc-4ad6-b2db-a8061b358813
-- title:
--   Lemma 3 — $g(d)\to 1$
-- statement:
--   For integers $d\ge 2$ define
--
--   $$
--   g(d)=\left(1+d^{-\frac{1}{2(k_d+1)}}\right)^{k_d}+\frac{2\sqrt d}{\ln d\left(1+\frac{\ln d}{2d}\right)^d},\qquad k_d=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil .
--   $$
--
--   Then $\lim_{d\to\infty} g(d)=1$.
--
--   The sequence $g(d)$ is the right-hand side of display (5); the lemma shows that the denominator of the first ratio of (3) at the parameter choice is eventually at most $4$.
--
--   Differences from the source:
--   - encoding: the sequence defined for integers d ≥ 2 → a sequence over all d : ℕ, limit along atTop; reason: the values at d = 0, 1 do not affect a limit; k_d is Nat.ceil, equal to the printed ceiling for d ≥ 2 (both are 0 at d = 2)
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Appendix A, Lemma 3, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace CongestionApproxPNE

/-- **Lemma 3: `g(d) → 1`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, Appendix A, Lemma 3, p.23: "For any integer d ≥ 2 define the sequence
g(d) = (1 + d^{−1/(2(kd+1))})^{kd} + 2√d/(ln d (1 + ln d/(2d))^d) where kd = ⌈ln d/(2 ln ln d)⌉.
Then lim_{d→∞} g(d) = 1."

**Formalization Note** The sequence is indexed by `d : ℕ` and the limit is along `atTop`
(the values at `d = 0, 1`, outside the paper's range `d ≥ 2`, do not affect a limit).
`k_d` is `kd d` (`Nat.ceil`); `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem lemma_3 :
    Tendsto (fun d : ℕ => (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d +
        2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d))
      atTop (𝓝 1) := by sorry

end CongestionApproxPNE
