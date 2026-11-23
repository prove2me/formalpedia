-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_Supplement_theorem_1_4
-- name    : FlowJobHardness.FlowShopGap.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:28:49.005887+00:00
-- url     : https://prove2.me/theorems/592c45f9-db6c-4b09-b63f-bda4db5ad315
-- title:
--   Theorem 1.4 — Both job-shop objectives: constant and logarithmic inapproximability
-- statement:
--   For general job shops, each of the objectives makespan and unweighted sum of completion times is NP-hard to approximate within any constant factor. Precisely, for every real $c\ge1$, the positive-rational-threshold promise
--   $$\operatorname{OPT}\le b\quad\hbox{versus}\quad\operatorname{OPT}>cb$$
--   is NP-hard under polynomial-time many-one reductions. In addition, for every $\epsilon>0$, a polynomial-time $O((\log\mathrm{lb})^{1-\epsilon})$ approximation for either objective implies
--   $$\mathrm{NP}\subseteq\mathrm{ZTIME}\!\left(2^{(\log n)^{O(1/\epsilon)}}\right).$$
--   The exponent coefficient is uniform in the small-$\epsilon$ regime; the approximation multiplier and eventual threshold are arbitrary. Jobs may revisit machines and have unrestricted operation counts.
--
--   Both the constant-factor and conditional logarithmic conclusions are retained in this companion theorem.
--
--   Differences from the source:
--   - encoding: Polynomial-time scheduling and standard machine complexity classes are stated without a concrete bit syntax. → Use binary rational instances and schedule outputs, published bounded Turing machines and genuine NP reductions; compare against every feasible real-time schedule.; reason: Specify the standard finite-input meaning while retaining zero durations, repeated visits and all comparison schedules.
--   - reading: The source uses asymptotic O((log lb)^(1−epsilon)) and ZTIME(2^((log n)^(O(1/epsilon)))). → Quantify a positive arbitrary approximation multiplier and threshold, and one positive time-exponent coefficient uniform for 0<epsilon<=1; use log2(max(2,lb)), n+2 and A/min(epsilon,1).; reason: Make all asymptotic constants and small-input conventions explicit without restricting the positive-epsilon domain; larger epsilon implies any smaller positive exponent guarantee.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:6, Theorem 1.4

import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

theorem theorem_1_4 :
    (∀ (o : Objective) (c : ℝ), 1 ≤ c →
      MeanBudgetXC.Supplement.PromiseNPHard (objectiveYes o) (objectiveNo o c)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ∀ o : Objective,
      HasLogApprox (jobDomain none) o ε → NPInZeroErrorTime (A / min ε 1)) := by sorry

end FlowJobHardness.FlowShopGap.Supplement
