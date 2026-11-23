-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_Supplement_theorem_1_5
-- name    : FlowJobHardness.FlowShopGap.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:31:32.6259+00:00
-- url     : https://prove2.me/theorems/7e0a6f32-bb01-498c-a544-0e7d7610b606
-- title:
--   Theorem 1.5 — A two-machine nonpreemptive PTAS implies deterministic quasi-polynomial NP
-- statement:
--   If the nonpreemptive two-machine job-shop makespan problem has a polynomial-time approximation scheme, then
--   $$\mathrm{NP}\subseteq\mathrm{DTIME}\!\left(n^{O(\log n)}\right).$$
--   A PTAS is one uniform computable scheme that returns a feasible schedule within $1+\epsilon$ of optimum in polynomial input-bit time for each fixed positive error; its polynomial degree may depend on the error. The input has exactly two machines, with arbitrary rational nonnegative durations and unrestricted repeated visits and numbers of operations per job.
--
--   The conclusion is the source's complexity implication, not a selected numerical gap, and it assumes neither $P\ne NP$ nor a bounded chain length.
--
--   Differences from the source:
--   - encoding: Polynomial-time scheduling and standard machine complexity classes are stated without a concrete bit syntax. → Use binary rational instances and schedule outputs, published bounded Turing machines and genuine NP reductions; compare against every feasible real-time schedule.; reason: Specify the standard finite-input meaning while retaining zero durations, repeated visits and all comparison schedules.
--   - encoding: A PTAS and DTIME(n^(O(log n))) use the usual fixed-error and asymptotic conventions. → One computable scheme has polynomial-time specializations for every positive rational error; the time-class union uses positive a,c and c(n+2)^(a log2(n+2)).; reason: Rational errors suffice by monotonicity; the shifted size and explicit constants change no asymptotic class.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:6, Theorem 1.5

import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Algorithms
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

theorem theorem_1_5 :
    HasPTAS (jobDomain (some 2)) false → NPInQuasipolynomialTime := by sorry

end FlowJobHardness.FlowShopGap.Supplement
