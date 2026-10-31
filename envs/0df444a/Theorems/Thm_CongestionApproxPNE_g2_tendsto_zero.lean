-- Prove2me | Theorems.Thm_CongestionApproxPNE_g2_tendsto_zero
-- name    : CongestionApproxPNE.g2_tendsto_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:13.405001+00:00
-- url     : https://prove2.me/theorems/b8ab920f-40f2-4468-9142-a27875b40d28
-- title:
--   Proof of Lemma 3 — $\lim_{d\to\infty} g_2(d)=0$
-- statement:
--   Let
--
--   $$
--   g_2(d)=\frac{2\sqrt d}{\left(1+\frac{\ln d}{2d}\right)^d\ln d}.
--   $$
--
--   Then $\lim_{d\to\infty} g_2(d)=0$. This is the second half of the proof of Lemma 3.
--
--   Differences from the source:
--   - encoding: the sequence defined for integers d ≥ 2 → a sequence over all d : ℕ, limit along atTop; reason: the values at d = 0, 1 do not affect a limit; k_d is Nat.ceil, equal to the printed ceiling for d ≥ 2 (both are 0 at d = 2)
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, p.24 (PDF p.25), "Next, we show that lim_{d→∞} g2(d) = 0."; g2 defined p.23 (PDF p.24)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace CongestionApproxPNE

/-- **`lim g₂(d) = 0`** (second half of the proof of Lemma 3).
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, p.24: "Next, we show that lim_{d→∞} g2(d) = 0." with, p.23,
"g2(d) = 2√d / ((1 + ln d/(2d))^d ln d)".

**Formalization Note** The sequence is indexed by `d : ℕ` and the limit is along `atTop`
(the values at `d = 0, 1`, outside the paper's range `d ≥ 2`, do not affect a limit).
`k_d` is `kd d` (`Nat.ceil`); `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem g2_tendsto_zero :
    Tendsto (fun d : ℕ => 2 * Real.sqrt d / ((1 + Real.log d / (2 * d)) ^ d * Real.log d))
      atTop (𝓝 0) := by sorry

end CongestionApproxPNE
