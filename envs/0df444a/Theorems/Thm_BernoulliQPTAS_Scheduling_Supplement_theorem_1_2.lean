-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_Supplement_theorem_1_2
-- name    : BernoulliQPTAS.Scheduling.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:27.864219+00:00
-- url     : https://prove2.me/theorems/ba080be3-1854-4090-a9c6-721adb5d91f5
-- title:
--   Theorem 1.2 — a PTAS for a constant number of distinct sizes
-- statement:
--   Consider Bernoulli jobs on $m$ identical machines, $0<m<N$: job $j$ has processing time $p_j$ with probability $q_j$ and $0$ otherwise, and $\mathrm{OPT}$ is the minimum expected sum of completion times over all adaptive, possibly randomized and idling policies. Let $n$ be the number of distinct sizes $p_j$ and $L$ the binary input length.
--
--   There are an absolute constant $c>0$ and an absolute degree $b$ such that for every $n$ and every $\eta\in(0,1]$ there is a constant $C_{n,\eta}$ with the following property. For every instance with exactly $n$ distinct sizes, the dynamic program of Theorem 4.6 run with $K=\lceil 1/\eta\rceil$ performs at most
--
--   $$
--   C_{n,\eta}\,(Nm)^{c\,n/\eta}\,(L+1)^{b}
--   $$
--
--   bit operations. Its table defines a lookup policy that is admissible and has expected cost at most $(1+\eta)\,\mathrm{OPT}$.
--
--   This is the polynomial-time approximation scheme for a constant number of sizes: for fixed $n$ and $\eta$ the running time is polynomial, with exponent linear in $n/\eta$. Its detailed form is Corollary 4.7.
--
--   **Formalization Note** The program is the published `computeRoundedPolicy`, charged in the published bit-operation model, and the lookup policy is the published `LookupPolicy`, exactly as in Theorem 4.6.
--
--   Differences from the source:
--   - reading: "time $(Nm)^{O(n/\eta)}\cdot\mathrm{poly}(L)$ for fixed $n$ and $\eta$" → ∃ absolute c > 0 and degree b, ∀ n, η ∃ C: cost ≤ C·(N·m)^{c·n/η}·(inputLength + 1)^b; reason: the O(·) and poly(·) constants are uniform; only the multiplicative constant may depend on the fixed n and η, as in the proof of Corollary 4.7
--   - encoding: "a (1+η)-approximation can be computed" → the fixed program computeRoundedPolicy I ⌈1/η⌉ of the published Theorem 4.6, whose table-lookup policy is admissible with cost ≤ (1+η)·OPT; reason: Corollary 4.7 takes K = ⌈1/η⌉ in Theorem 4.6; the algorithm is displayed, not existential
--   - encoding: standing assumption m < N of Section 1.1 → hypotheses 0 < m and m < N; reason: same instances
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Theorem 1.2, p. 3; detailed form Corollary 4.7 and proof, p. 13

import Definitions.Def_BernoulliQPTAS_Scheduling_Program

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling

theorem theorem_1_2 :
    ∃ (c : ℝ) (b : ℕ), 0 < c ∧ ∀ n : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ C : ℝ,
      ∀ {N m : ℕ} (I : Instance N m), 0 < m → m < N → (sizeClasses I).card = n →
        let out := computeRoundedPolicy I ⌈1 / η⌉₊
        (out.cost : ℝ) ≤ C * ((N : ℝ) * m) ^ (c * n / η) * ((inputLength I : ℝ) + 1) ^ b ∧
        ∃ t : PolicyTree N m,
          LookupPolicy out.val (N + 1) out.val.root (fun _ => 0) t ∧
          Admissible I (initialState Finset.univ) t ∧
          treeCost I t ≤ ENNReal.ofReal (1 + η) * optimum I (initialState Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling.Supplement
