-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_Supplement_theorem_5_1
-- name    : BernoulliQPTAS.Scheduling.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:37.734029+00:00
-- url     : https://prove2.me/theorems/d7f8d0ba-7e4f-44e3-b08f-9933ff329250
-- title:
--   Theorem 5.1 (with Theorem 1.3) — the adaptive priority rule is a $\min\{m,1+\Lambda\}$-approximation in polynomial time
-- statement:
--   Consider Bernoulli jobs on $m\ge1$ identical machines, with $P=\sum_jq_jp_j$, $\Lambda=\sum_jq_j$, and $\mathrm{OPT}$ the minimum expected sum of completion times over all adaptive, possibly randomized and idling policies. Fix distinct ranks $\rho(j)$, and let $G$ be the adaptive priority rule of Section 5 (non-idling, always starting a remaining job minimizing $(q_j\min\{p_j,\theta\},q_j,\rho(j))$, where $\theta$ is the minimum of the $m-1$ largest realized processing times so far padded with zeros; SEPT for $m=1$).
--
--   1. $G$ is an admissible non-idling policy and
--   $$
--   \mathrm{cost}(G)-P\le\min\{m,1+\Lambda\}\,(\mathrm{OPT}-P),\qquad \mathrm{cost}(G)\le\min\{m,1+\Lambda\}\,\mathrm{OPT}.
--   $$
--   2. (Theorem 1.3, running time.) There are constants $C,b$ such that for every instance with $0<m<N$, every ranks $\rho$ and every realization $\omega$, an explicit implementation of $G$ reproduces the actions of $G$ on $\omega$ (job, machine, start time) using at most $C\,(L+\sum_j\mathrm{bits}(\rho(j))+1)^b$ bit operations, where $L$ is the binary input length.
--
--   The theorem gives a ratio independent of $N$ in polynomial time. The ratio is $2$ for two machines, and the second bound is useful when few jobs are expected to be positive.
--
--   **Formalization Note** $\mathrm{OPT}-P$ is a truncated difference of extended nonnegative reals. Since $\mathrm{OPT}\ge P$ (Lemma 2.2), nothing is truncated, and the bound $\mathrm{cost}(G)\le P+\min\{m,1+\Lambda\}(\mathrm{OPT}-P)$ is the first claim. The implementation is the explicit program `greedyRun`, charged in the published bit-operation model. With the ranks taken as job labels, $\sum_j\mathrm{bits}(\rho(j))$ is polynomial in $L$.
--
--   Differences from the source:
--   - encoding: cost(G) − P ≤ min{m, 1+Λ}·(OPT − P) → treeCost G ≤ P + c·(OPT − P) in ℝ≥0∞ with c = ofReal(min(m, 1+Λ)); reason: P is finite and OPT ≥ P (Lemma 2.2), so this is the same inequality
--   - reading: "For m = 1, G is SEPT" (tie-breaking not specified) → for m = 1 the first key is μ_j, with ties broken by q_j and then ρ(j); reason: on one machine every SEPT tie-breaking has the same expected cost, so the claim is the same
--   - generalization: Section 1.1 standing assumption m < N → the cost bounds for every m ≥ 1; reason: the source states the theorem "for every instance"; the case m < N is included
--   - encoding: "runs in polynomial time" (Theorem 1.3; O(N²) arithmetic operations, p. 14) → for 0 < m < N, a fixed charged program reproducing G’s actions on every realization with cost ≤ C·(inputLength + Σ_j bits(ρ_j) + 1)^b, with C and b uniform; reason: the ranks are part of the rule’s input; with labels as ranks their total bit length is polynomial in L
--   - encoding: "whenever a machine is free" (machine not specified) → the lowest-labeled machine among those released earliest; reason: machines are identical, so the choice does not affect the cost
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Theorem 5.1, p. 14 (policy G and O(N²) remark, p. 14; proof pp. 14–16); Theorem 1.3, p. 3

import Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Greedy

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling

theorem theorem_5_1 :
    (∀ {N m : ℕ} (I : Instance N m), 0 < m → ∀ ρ : Fin N → ℕ, Function.Injective ρ →
      let G := greedyPolicy I ρ
      let P := totalMean I Finset.univ
      let OPT := optimum I (initialState Finset.univ)
      let c := ENNReal.ofReal (min (m : ℝ) (1 + (sumProb I : ℝ)))
      Admissible I (initialState Finset.univ) G ∧ NonIdling I (initialState Finset.univ) G ∧
        treeCost I G ≤ P + c * (OPT - P) ∧ treeCost I G ≤ c * OPT) ∧
    ∃ C b : ℕ, ∀ {N m : ℕ} (I : Instance N m), 0 < m → m < N →
      ∀ ρ : Fin N → ℕ, Function.Injective ρ → ∀ ω : Outcome N,
        ((greedyRun I ρ ω).val.map fun a => (a.1, a.2.1, (a.2.2 : ℝ))) =
            (trace (greedyPolicy I ρ) ω).map (fun a => (a.job, a.machine.val, (a.time : ℝ))) ∧
          (greedyRun I ρ ω).cost ≤ C * (inputLength I + ∑ j, natBits (ρ j) + 1) ^ b := by sorry

end BernoulliQPTAS.Scheduling.Supplement
