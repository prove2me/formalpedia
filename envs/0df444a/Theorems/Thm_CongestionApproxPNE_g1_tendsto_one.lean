-- Prove2me | Theorems.Thm_CongestionApproxPNE_g1_tendsto_one
-- name    : CongestionApproxPNE.g1_tendsto_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:58.273784+00:00
-- url     : https://prove2.me/theorems/93d8ef0b-94c4-48fd-860d-038464b73c8c
-- title:
--   Proof of Lemma 3 — $\lim_{d\to\infty} g_1(d)=1$
-- statement:
--   Let $g_1(d)=\left(1+d^{-\frac{1}{2(k_d+1)}}\right)^{k_d}$, where $k_d=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil$. Then
--
--   $$
--   \lim_{d\to\infty} g_1(d)=1 .
--   $$
--
--   This is the first half of the proof of Lemma 3.
--
--   Differences from the source:
--   - encoding: the sequence defined for integers d ≥ 2 → a sequence over all d : ℕ, limit along atTop; reason: the values at d = 0, 1 do not affect a limit; k_d is Nat.ceil, equal to the printed ceiling for d ≥ 2 (both are 0 at d = 2)
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, p.24 (PDF p.25), "First, we show lim_{d→∞} g1(d) = 1."; g1 defined p.23 (PDF p.24)

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace CongestionApproxPNE

/-- **`lim g₁(d) = 1`** (first half of the proof of Lemma 3).
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, Appendix A, proof of Lemma 3, p.24: "First, we show lim_{d→∞} g1(d) = 1." with, p.23,
"g1(d) = (1 + d^{−1/(2(kd+1))})^{kd}".

**Formalization Note** The sequence is indexed by `d : ℕ` and the limit is along `atTop`
(the values at `d = 0, 1`, outside the paper's range `d ≥ 2`, do not affect a limit).
`k_d` is `kd d` (`Nat.ceil`); `Real.log` is `ln`; non-integer powers of `d` are `Real.rpow`. -/
theorem g1_tendsto_one :
    Tendsto (fun d : ℕ => (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d)
      atTop (𝓝 1) := by sorry

end CongestionApproxPNE
