-- Prove2me | Theorems.Thm_BanditAlgorithm_klDiv_banditStepKernel_eq_sum
-- name    : BanditAlgorithm.klDiv_banditStepKernel_eq_sum
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:34:17.297458+00:00
-- url     : https://prove2.me/theorems/4e5e05d0-ecae-4dba-ae28-fb09e7853605
-- title:
--   One-round divergence of the canonical bandit model
-- statement:
--   One round of the canonical bandit model costs exactly the policy-weighted average of the arm divergences.
--
--   Fix a policy $\pi$ and two bandit environments $\nu=(P_i)_{i=1}^k$ and $\nu'=(P_i')_{i=1}^k$ with $D(P_i,P_i')<\infty$ for every arm. Condition on a history $h$ of $n$ completed rounds, and let $\pi(\cdot\mid h)$ be the distribution of the arm played next. The law of the next round's (arm, reward) pair is a Markov kernel in each environment, and
--
--   $$
--   D\Big(\big(\pi\otimes P\big)(\cdot\mid h)\;\Big\Vert\;\big(\pi\otimes P'\big)(\cdot\mid h)\Big)
--   \;=\;\sum_{i=1}^{k}\pi(i\mid h)\,D(P_i,P_i').
--   $$
--
--   The policy is the same in both environments, so its factor cancels from the likelihood ratio and contributes nothing; what remains is the divergence of the reward distribution of whichever arm was chosen, averaged over the choice.
--
--   This is the per-round content of the divergence decomposition of Lattimore and Szepesvari's Lemma 15.1: the full decomposition $D(\mathbb P_{\nu\pi},\mathbb P_{\nu'\pi})=\sum_i \mathbb E_\nu[T_i(n)]D(P_i,P_i')$ is obtained by summing this identity over rounds. Stated on its own it can be applied round by round, which is what any localised or stopping-time version of the decomposition needs.
--
--   **Formalization Note** The hypothesis that each arm divergence is finite gives absolute continuity $P_i\ll P_i'$, which is what makes the one-round Radon-Nikodym derivative $(a,x)\mapsto \frac{dP_a}{dP_a'}(x)$ available; the finiteness itself is not otherwise used, and the identity holds in $[0,\infty]$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Lemma 15.1 and Eq. (15.2), printed pp. 198-199 (the conditional one-round computation, where the policy factors cancel from the likelihood ratio).

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Definitions.Def_BanditPolicy

open MeasureTheory ProbabilityTheory InformationTheory

theorem BanditAlgorithm.klDiv_banditStepKernel_eq_sum {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  sorry
