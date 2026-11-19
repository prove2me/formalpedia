-- Prove2me | Theorems.Thm_APSCounting893_Main_sampled_resultant_degree_bound
-- name    : APSCounting893.Main.sampled_resultant_degree_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T20:05:14.930414+00:00
-- url     : https://prove2.me/theorems/5e1ea2f2-28e1-4ef2-861b-3e08e3133883
-- title:
--   The sampled resultant degree bound (6.3)
-- statement:
--   Let $I$ be a reduced rational circuit with $n>0$ input variables and $n+1$ outputs, let $L$ be the length of its binary circuit encoding, and let $\theta$ be any integer tuple of auxiliary parameters. Put $N=2n+1$ and let $d$ be the maximum of $2$ and the circuit's output formal degrees. For the actual normalized homogeneous resultant $R_\theta$ used in the APS construction,
--
--   $$\deg R_\theta\le D_*=(N+1)(2N+1)d^N\le 2^{32(L+1)^2}.$$
--
--   The bounds hold for every parameter tuple, including choices for which the resultant vanishes or the geometric projection is unsuccessful. This supplies the degree component of uniform resultant coefficient access; it imposes no polynomial bound on the expanded degree.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 6.2, equation (6.3), p. 24, and Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. The explicit polynomial 32(L+1)^2 bounds the singly exponential estimate in (6.3).

import Definitions.Def_APSCounting893_Main_SampledResultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.sampled_resultant_degree_bound
    (I : ReducedCircuit) (theta : SampleTuple I) :
    (sampledResultant I theta).totalDegree ≤ sourceDStar I.n I.rawMap.d ∧
      sourceDStar I.n I.rawMap.d ≤ 2 ^ polyBound 32 2 I.C.encode.length := by sorry
