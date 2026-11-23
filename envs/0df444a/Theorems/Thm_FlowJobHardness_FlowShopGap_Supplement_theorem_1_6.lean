-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_Supplement_theorem_1_6
-- name    : FlowJobHardness.FlowShopGap.Supplement.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:33:21.004966+00:00
-- url     : https://prove2.me/theorems/a22d1507-bed6-4dcd-aa36-dad160edcb28
-- title:
--   Theorem 1.6 — A three-machine preemptive PTAS implies deterministic quasi-polynomial NP
-- statement:
--   If the preemptive three-machine job-shop makespan problem has a polynomial-time approximation scheme, then
--   $$\mathrm{NP}\subseteq\mathrm{DTIME}\!\left(n^{O(\log n)}\right).$$
--   The instance has exactly three machines; jobs have unrestricted operation counts and may revisit machines. Each operation may be interrupted and resumed on its assigned machine without losing work, subject to chain precedence and machine capacity. The scheme returns finitely encoded rational processing intervals, compared with every feasible real-time preemptive schedule, including arbitrary measurable processing sets.
--
--   This is the existential no-PTAS consequence proved in the source. It imposes no integer-breakpoint hypothesis, does not infer preemptive hardness from nonpreemptive hardness, and invents no numerical hardness ratio.
--
--   Differences from the source:
--   - encoding: Polynomial-time scheduling and standard machine complexity classes are stated without a concrete bit syntax. → Use binary rational instances and schedule outputs, published bounded Turing machines and genuine NP reductions; compare against every feasible real-time schedule.; reason: Specify the standard finite-input meaning while retaining zero durations, repeated visits and all comparison schedules.
--   - encoding: A PTAS and DTIME(n^(O(log n))) use the usual fixed-error and asymptotic conventions. → One computable scheme has polynomial-time specializations for every positive rational error; the time-class union uses positive a,c and c(n+2)^(a log2(n+2)).; reason: Rational errors suffice by monotonicity; the shifted size and explicit constants change no asymptotic class.
--   - encoding: Preemption permits interruption and resumption without penalty; the source does not specify a set-theoretic execution representation. → Use arbitrary measurable processing sets in finite start/finish windows; recorded finishes may include idle padding, and returned schedules use finite rational interval lists.; reason: Finite operation windows partition time into finitely many cells; work in each cell can be serialized per machine without changing any precedence window or increasing completion bounds. Padding therefore changes no optimum, and rational data admit finite rational optimal schedules.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:7, Theorem 1.6

import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

theorem theorem_1_6 :
    HasPTAS (jobDomain (some 3)) true → NPInQuasipolynomialTime := by sorry

end FlowJobHardness.FlowShopGap.Supplement
