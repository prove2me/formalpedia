-- Prove2me | Theorems.Thm_DiscServLine_SPT_corollary_1_lower_bound
-- name    : DiscServLine.SPT.corollary_1_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:28.540935+00:00
-- url     : https://prove2.me/theorems/0b7c1141-ad7e-4c52-bd04-a6821020ea75
-- title:
--   Corollary 1, p. 17 (PDF 17) — the SPT queue length is at least ½(ln(1 − Λ₁))²
-- statement:
--   Consider any service line with demand measure $\mu$ on $[\underline t,\bar t]\subseteq[0,\infty)$ and load $\Lambda_1<1$, served under non-preemptive SPT. Its expected queue length $Q=\int W\,d\mu$ satisfies
--   $$Q\ \ge\ \tfrac12\{\ln(1-\Lambda_1)\}^2 .$$
--   The bound depends on the load only, not on the throughput $\Lambda_0$ or on the second moment $\Lambda_2$.
--
--   This is the lower-bound half of Corollary 1: the minimum SPT queue length over all demand schedules with given $\Lambda_0$ and $\Lambda_1$ is $\tfrac12\{\ln(1-\Lambda_1)\}^2$. The companion statement `corollary_1_attained` shows that the bound is attained.
--
--   **Formalization Note** The service line ranges over all admissible demand measures, including those with atoms (single services), with the Cobham waiting time at atoms.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 17 (PDF 17), Corollary 1 (proof: p. 42 (PDF 42), printed as "Corollary 2")

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem corollary_1_lower_bound (d : Design) (hd : Admissible d) :
    (1 / 2 : ℝ) * (Real.log (1 - d.Λk 1)) ^ 2 ≤ d.Q := by sorry

end DiscServLine.SPT
