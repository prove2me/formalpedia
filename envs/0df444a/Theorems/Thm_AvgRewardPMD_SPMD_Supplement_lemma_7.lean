-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_lemma_7
-- name    : AvgRewardPMD.SPMD.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:27:33.997521+00:00
-- url     : https://prove2.me/theorems/ede38f97-27e9-491c-8f72-e7960cbef92e
-- title:
--   Lemma 7, p. 18 — under Assumption 2 there are C_P > 0, ϱ ∈ (0,1) with ν^π > 0 and max_s‖(P_π)^t(s,·) − ν^π‖₁ ≤ C_Pϱ^t for every policy π and t ≥ 1
-- statement:
--   Let $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ be a finite AMDP satisfying the mixing Assumption 1 and the ergodicity Assumption 2: for every feasible policy $\pi$ the chain $P_\pi(s,s')=\sum_a\pi(a\mid s)\mathsf P(s'\mid s,a)$ is irreducible and aperiodic. Then there exist constants $C_P>0$ and $\varrho\in(0,1)$ such that for every feasible policy $\pi$ and every stationary distribution $\nu^\pi$ of $P_\pi$, $\nu^\pi(s)>0$ for all $s$, and
--   $$\max_{s\in\mathcal S}\big\|(P_\pi)^t(s,\cdot)-\nu^\pi\big\|_1\le C_P\varrho^t\qquad\text{for all }t\in\mathbb Z_+ .$$
--
--   The constants are common to all policies; they set the sample-skipping lengths $\tau,\tau'$ of VRTD (Theorem 4) and bound the mixing time of Assumption 1 by $O(\log C_P/\log(1/\varrho))$.
--
--   **Formalization Note** $\mathbb Z_+$ is read as $t\ge1$, as for the inputs $\tau,\tau'\in\mathbb Z_+$ of Algorithm 3. The maximum over $s$ is a bound for every $s$. Under Assumption 2 the stationary distribution is unique; the statement covers every stationary distribution.
--
--   Differences from the source:
--   - encoding: ν^π, the stationary distribution → every stationary distribution ν of P_π; reason: under Assumption 2 the stationary distribution exists and is unique
--   - reading: t ∈ Z+ → t ≥ 1; reason: the paper uses Z+ for positive integers (τ, τ′, N_k ∈ Z+ in Algorithm 3)
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 18, Lemma 7 (citing Bertsekas–Tsitsiklis 1995)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning

theorem lemma_7 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (herg : IsErgodic P) :
    ∃ CP : ℝ, 0 < CP ∧ ∃ ϱ : ℝ, 0 < ϱ ∧ ϱ < 1 ∧
      ∀ π : S → A → ℝ, IsPolicy π →
        ∀ ν : S → ℝ, MarkovMixing.IsStationary (stateMatrix P π) ν →
          (∀ s, 0 < ν s) ∧
          ∀ t : ℕ, 1 ≤ t → ∀ s : S,
            ∑ s', |((stateMatrix P π) ^ t) s s' - ν s'| ≤ CP * ϱ ^ t := by sorry

end AvgRewardPMD.SPMD.Supplement
