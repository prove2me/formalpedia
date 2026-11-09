-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_theorem_1_1
-- name    : BernoulliQPTAS.Scheduling.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:52.643515+00:00
-- url     : https://prove2.me/theorems/ea33dac7-a7a0-4fa1-b1d6-4764fbd01b98
-- title:
--   Theorem 1.1 — a QPTAS for every number of machines
-- statement:
--   Consider Bernoulli jobs on $m$ identical machines, with $N$ jobs and $1\le m<N$, and let $L$ be the binary input length. There are constants $C,a>0$ and $b$, fixed before the instance and the accuracy, such that for every real $\eta\in(0,1]$ the charged preprocessing program on input the instance and the integer $\lceil 1/\eta\rceil$ runs in time at most
--
--   $$C\cdot 2^{a\,\eta^{-2}\log_2^2(N/\eta)}\cdot(L+1)^b,$$
--
--   and the policy $\Pi$ defined by reading the returned table, one read per decision, is physically admissible and has
--
--   $$\operatorname{cost}(\Pi)\le(1+\eta)\operatorname{OPT},$$
--
--   where OPT is the infimum over all admissible adaptive policies, including randomized and deliberately idling ones. This is the main result of the paper.
--
--   Differences from the source:
--   - encoding: time 2^{O(η^{-2} log²(N/η))} · poly(L) with O and poly constants unstated → ∃ C a : ℝ and b : ℕ quantified before N, m, I and η, bounding the charge of qptasProgram by C · 2^(a η^{-2} (log₂(N/η))²) · (L + 1)^b; reason: uniform constants express the source computational class; the charge is that of the specified program, in the semantics of the Program definition
--   - encoding: real accuracy η ∈ (0, 1] read by the algorithm → the program receives the integer ⌈1/η⌉₊, for every real η in (0, 1]; reason: Section 4.5 replaces η by 1/⌈1/η⌉; no real number is computed with, and every requested accuracy is covered
--   - encoding: Each decision of the policy is a table lookup → the policy is the tree t satisfying LookupPolicy on the returned table; reason: LookupPolicy states that each started job is named by one read at the current address, and machine, time and next address follow from the maintained releases and the observed outcome
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Theorem 1.1, p. 3; proof pp. 13–14; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Program

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem theorem_1_1 :
    ∃ (C a : ℝ) (b : ℕ), 0 < C ∧ 0 < a ∧
      ∀ {N m : ℕ} (I : Instance N m), 0 < m → m < N → ∀ η : ℝ, 0 < η → η ≤ 1 →
        let out := qptasProgram I ⌈1 / η⌉₊
        (out.cost : ℝ) ≤ C * (2 : ℝ) ^ (a * (η⁻¹) ^ 2 * (Real.logb 2 (N / η)) ^ 2) *
          ((inputLength I : ℝ) + 1) ^ b ∧
        ∃ t : PolicyTree N m,
          LookupPolicy out.val (N + 1) out.val.root (fun _ => 0) t ∧
          Admissible I (initialState Finset.univ) t ∧
          treeCost I t ≤ ENNReal.ofReal (1 + η) * optimum I (initialState Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling
