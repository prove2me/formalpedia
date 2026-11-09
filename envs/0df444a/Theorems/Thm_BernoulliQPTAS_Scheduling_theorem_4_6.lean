-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_theorem_4_6
-- name    : BernoulliQPTAS.Scheduling.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:35.126507+00:00
-- url     : https://prove2.me/theorems/5981f426-614f-42ef-b44f-facfea70d4d3
-- title:
--   Theorem 4.6 — computed rounded-release policy
-- statement:
--   Let an instance have $N$ jobs, $1\le m<N$ machines and $n$ size classes of cardinalities $N_c$, and let $K\ge1$ be an integer. There are constants $C,b$, fixed before all of these, such that the charged program that builds the table of the dynamic program runs in time at most
--
--   $$C\binom{(K+1)N+n-1}{n}\binom{m+n(K+1)-1}{n(K+1)-1}\prod_{c=1}^n(N_c+1)\,(N+m+L+1)^b,$$
--
--   where $L$ is the binary length of the instance and of $K$. The policy $\Pi$ defined by reading the returned table, one read per decision, is physically admissible and satisfies
--
--   $$\operatorname{cost}(\Pi)\le P+\Bigl(1+\frac1K\Bigr)(\operatorname{OPT}-P).$$
--
--   Here OPT is the infimum over all admissible adaptive policies, including randomized and deliberately idling ones.
--
--   Differences from the source:
--   - encoding: computed in time … · poly(N, m, L) with O and poly constants unstated → ∃ C b : ℕ quantified before N, m, I and K, bounding the charge of the program computeRoundedPolicy by C times the three exact factors times (N + m + L + bits(K) + 1)^b; reason: uniform constants express the source computational class; the charge is that of the specified program, in the semantics of the Program definition
--   - reading: L is the input length → the instance length inputLength I together with the binary length of K; reason: K is an input of the computation in this theorem, and the proof on p.13 uses numbers with denominator K · lcm, whose bit length depends on K
--   - encoding: Each decision of Π is then a table lookup → the policy is the tree t satisfying LookupPolicy on the returned table; reason: LookupPolicy states that each started job is named by one read at the current address, and machine, time and next address follow from the maintained releases and the observed outcome
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Theorem 4.6, p. 13; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Program

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem theorem_4_6 :
    ∃ C b : ℕ, 0 < C ∧ ∀ {N m : ℕ} (I : Instance N m), 0 < m → m < N → ∀ K : ℕ, 1 ≤ K →
      let n := (sizeClasses I).card
      let out := computeRoundedPolicy I K
      out.cost ≤ C * (Nat.choose ((K + 1) * N + n - 1) n *
          Nat.choose (m + n * (K + 1) - 1) (n * (K + 1) - 1) *
          ∏ p ∈ sizeClasses I, (classCount I p + 1)) *
        (N + m + inputLength I + natBits K + 1) ^ b ∧
      ∃ t : PolicyTree N m,
        LookupPolicy out.val (N + 1) out.val.root (fun _ => 0) t ∧
        Admissible I (initialState Finset.univ) t ∧
        treeCost I t ≤ totalMean I Finset.univ +
          ENNReal.ofReal (1 + 1 / (K : ℝ)) *
            (optimum I (initialState Finset.univ) - totalMean I Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling
