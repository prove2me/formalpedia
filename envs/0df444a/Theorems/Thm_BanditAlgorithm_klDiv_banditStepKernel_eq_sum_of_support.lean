-- Prove2me | Theorems.Thm_BanditAlgorithm_klDiv_banditStepKernel_eq_sum_of_support
-- name    : BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T17:07:02.923856+00:00
-- url     : https://prove2.me/theorems/d7ebca60-fe1f-4f7c-8bb6-42b058135bae
-- title:
--   One-round divergence, with finiteness only on the policy's support
-- statement:
--   One round of the canonical bandit model costs the policy-weighted average of the arm divergences — with the finiteness hypothesis required only of the arms the policy can actually play.
--
--   Fix a policy $\pi$, two environments $\nu=(P_i)_{i=1}^k$, $\nu'=(P_i')_{i=1}^k$, and a history $h$ of $n$ completed rounds. Assume $D(P_i,P_i')<\infty$ for every arm $i$ that $\pi(\cdot\mid h)$ gives positive probability. Then
--
--   $$
--   D\Big(\big(\pi\otimes P\big)(\cdot\mid h)\;\Big\Vert\;\big(\pi\otimes P'\big)(\cdot\mid h)\Big)
--   \;=\;\sum_{i=1}^{k}\pi(i\mid h)\,D(P_i,P_i').
--   $$
--
--   Restricting the hypothesis to the support of the policy is what makes the identity applicable in general. An arm the learner never plays in this round may have $D(P_i,P_i')=\infty$ — the two environments may even be mutually singular on that arm — without affecting either side: on the right its term is $0\cdot\infty=0$, and on the left the round's law never sees it. Demanding finiteness for *all* arms would rule out exactly these situations, which arise whenever a policy deterministically avoids an arm.
--
--   **Formalization Note** In $[0,\infty]$ the convention $0\cdot\infty=0$ is what makes the sum on the right well behaved; no finiteness is asserted for unplayed arms. The proof needs absolute continuity of the reward distributions only for almost every arm drawn from $\pi(\cdot\mid h)$, which is exactly the stated hypothesis, since on a finite arm set almost every drawn arm has positive probability.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Lemma 15.1 and Eq. (15.2), printed pp. 198-199 (the conditional one-round computation, where the policy factors cancel from the likelihood ratio).

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Definitions.Def_BanditPolicy

open MeasureTheory ProbabilityTheory InformationTheory

theorem BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (pi : BanditPolicy k) (h : BanditHistory k n)
    (hKL : ∀ i, (pi.select n h) {i} ≠ 0 → klDiv (nu.P i) (nu'.P i) ≠ ⊤) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  sorry
