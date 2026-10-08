-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_theorem_5_2
-- name    : ArapostathisAC.VanishingDiscount.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:17:23.947511+00:00
-- url     : https://prove2.me/theorems/85c6cb16-e079-43e9-be1c-958c3f74e194
-- title:
--   Theorem 5.2 — uniformly bounded differential discounted values give a bounded solution of the ACOE
-- statement:
--   Consider the countable-state controlled Markov process of §5: states $S=\{0,1,2,\dots\}$, compact nonempty action sets $U(i)$, nonnegative costs $c(i,a)$ and transition probabilities $P(j\mid i,a)$ continuous in $a\in U(i)$. For $0<\beta<1$ let $J^*_\beta(i)$ be the optimal $\beta$-discounted cost from state $i$ over all admissible policies, assumed finite, and let
--   $$h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$$
--   be the differential discounted value function. Suppose there is a constant $K>0$ such that $|h_\beta(i)|\le K$ for all $\beta\in(0,1)$ and $i\in S$. Then there are $\rho\in\mathbb R$ and a function $h:S\to\mathbb R$ such that
--
--   1. $(\rho,h)$ is a bounded solution of the average cost optimality equation
--   $$\rho+h(i)=\min_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)h(j)\Big\},\qquad i\in S;$$
--   2. for some sequence $\beta_n\in(0,1)$ with $\beta_n\to1$, $h(i)=\lim_{n\to\infty}h_{\beta_n}(i)$ for every $i\in S$;
--   3. $\lim_{\beta\to1}(1-\beta)J^*_\beta(i)=\rho$ for every $i\in S$.
--
--   This is the basic vanishing discount theorem: a uniform bound on the differential discounted values turns the discounted optimality equations into a bounded solution of the average cost optimality equation, and the scaled discounted values converge to its constant.
--
--   **Formalization Note.** The paper's hypothesis $|h_\beta(i)|\le K$ presupposes that $J^*_\beta$ is finite; this is a stated hypothesis, because Lean's `toReal` would send $+\infty$ to $0$ and let the bound hold by a junk value. The three conclusions share one pair $(\rho,h)$. A solution of the ACOE requires every series to converge and the minimum to be attained. In (iii) the limit is the one-sided limit $\beta\uparrow1$ along all of $(0,1)$, not along a subsequence. $J^*_\beta$ is the infimum over all history-dependent randomized admissible policies.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 301, Theorem 5.2 (h_β defined on the same page; the ACOE is (5.1), p. 299)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open Filter Topology

namespace ArapostathisAC.VanishingDiscount

theorem theorem_5_2 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hfin : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, discValue M β i ≠ ⊤)
    (K : ℝ) (hK : 0 < K) (hbd : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ K) :
    ∃ ρ : ℝ, ∃ h : ℕ → ℝ, ∃ β : ℕ → ℝ,
      (ACOE M ρ h ∧ ∃ C, ∀ i, |h i| ≤ C) ∧
      ((∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto β atTop (𝓝 1) ∧
        ∀ i, Tendsto (fun n => hRel M (β n) i) atTop (𝓝 (h i))) ∧
      ∀ i, Tendsto (fun b => (1 - b) * (discValue M b i).toReal) (𝓝[<] 1) (𝓝 ρ) := by sorry

end ArapostathisAC.VanishingDiscount
