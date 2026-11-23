-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_Supplement_theorem_1_3
-- name    : FlowJobHardness.FlowShopGap.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:27:47.35911+00:00
-- url     : https://prove2.me/theorems/d8c84f20-c61d-4519-b2bf-d612df23de53
-- title:
--   Theorem 1.3 — Both generalized-flow-shop objectives: logarithmic inapproximability
-- statement:
--   For either generalized-flow-shop objective $V=C_{\max}$ or $V=\sum_j C_j$, existence of a polynomial-time $O((\log\mathrm{lb})^{1-\epsilon})$ approximation algorithm, with arbitrary fixed multiplier and eventual threshold, implies
--   $$\mathrm{NP}\subseteq\mathrm{ZTIME}\!\left(2^{(\log n)^{O(1/\epsilon)}}\right).$$
--   Here $n$ in the time class is the input bit length. The formal statement chooses one positive exponent coefficient $A$, uniformly in $\epsilon$ and in the objective, and uses exponent $A/\min\{\epsilon,1\}$, covering every $\epsilon>0$. Zero-error means every halting random branch is correct with finite expected execution time.
--
--   The result preserves both objectives and the full computational consequence of the source. No assertion of failure-detection, reduction computability or hardness is assumed as a premise.
--
--   Differences from the source:
--   - encoding: Polynomial-time scheduling and standard machine complexity classes are stated without a concrete bit syntax. → Use binary rational instances and schedule outputs, published bounded Turing machines and genuine NP reductions; compare against every feasible real-time schedule.; reason: Specify the standard finite-input meaning while retaining zero durations, repeated visits and all comparison schedules.
--   - reading: The source uses asymptotic O((log lb)^(1−epsilon)) and ZTIME(2^((log n)^(O(1/epsilon)))). → Quantify a positive arbitrary approximation multiplier and threshold, and one positive time-exponent coefficient uniform for 0<epsilon<=1; use log2(max(2,lb)), n+2 and A/min(epsilon,1).; reason: Make all asymptotic constants and small-input conventions explicit without restricting the positive-epsilon domain; larger epsilon implies any smaller positive exponent guarantee.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:6, Theorem 1.3

import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

theorem theorem_1_3 :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ∀ o : Objective,
      HasLogApprox flowDomain o ε → NPInZeroErrorTime (A / min ε 1) := by sorry

end FlowJobHardness.FlowShopGap.Supplement
