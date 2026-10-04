-- Prove2me | Theorems.Thm_Aumann1987_TwoPerson_devCond_iff_condPayoff
-- name    : Aumann1987.TwoPerson.devCond_iff_condPayoff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:27:18.200446+00:00
-- url     : https://prove2.me/theorems/fbc77a1b-1e49-43ad-8532-4e0269f3089d
-- title:
--   Proposition 2.3, proof — (2.2) holds iff it holds conditionally on each possible suggestion
-- statement:
--   Let $(p_{jk})$ be a distribution on $S^1\times S^2$ and let $h^1,h^2$ be the payoffs. A suggestion $j$ to player 1 is *possible* if $\sum_k p_{jk}>0$, and then $H^1(q\mid j)=\sum_k h^1_{qk}p_{jk}/\sum_k p_{jk}$ is player 1's conditional expected payoff from playing $q$; likewise $H^2(r\mid k)=\sum_j h^2_{jr}p_{jk}/\sum_j p_{jk}$ for a possible suggestion $k$ to player 2 ($\sum_j p_{jk}>0$). Then:
--
--   1. player 1's equilibrium condition (2.2) written on $p$ (no $\varphi:S^1\to S^1$ increases $\sum_j\sum_k p_{jk}h^1_{\varphi(j)k}$ above $\sum_j\sum_k p_{jk}h^1_{jk}$) holds if and only if
--   $$H^1(q\mid j)\le H^1(j\mid j)\quad\text{for every possible }j\in S^1\text{ and every }q\in S^1;$$
--   2. player 2's condition holds if and only if $H^2(r\mid k)\le H^2(k\mid k)$ for every possible $k\in S^2$ and every $r\in S^2$.
--
--   This is the first step of the proof of Proposition 2.3: the equilibrium condition is equivalent to obedience being optimal after each suggestion that occurs with positive probability.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 6 (PDF p. 7), Proposition 2.3, proof (conditioning on each possible suggestion)

import Mathlib
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

namespace Aumann1987.TwoPerson

/-- **Conditioning on possible suggestions** (Aumann 1987, Proposition 2.3, proof, p. 6, PDF p. 7:
"For (2.2) it is necessary and sufficient that for each i, the expectation still obeys the
inequality when conditioned on each possible value of fⁱ"). For a distribution `p`:
player 1's condition (2.2) on `p` holds iff for every possible suggestion `j` (`∑_k p_{jk} > 0`)
and every action `q`, `H¹(q|j) ≤ H¹(j|j)`; and player 2's holds iff for every possible
suggestion `k` (`∑_j p_{jk} > 0`) and every `r`, `H²(r|k) ≤ H²(k|k)`.

Formalization Note: impossible suggestions are excluded by the hypothesis `0 < ∑ …`, as in the
paper, so the convention `x / 0 = 0` in `condPayoff₁`, `condPayoff₂` is never used. -/
theorem devCond_iff_condPayoff {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (h₁ h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    (DevCond₁ h₁ p ↔
      ∀ j : S₁, 0 < ∑ k, p j k → ∀ q : S₁, condPayoff₁ h₁ p q j ≤ condPayoff₁ h₁ p j j) ∧
    (DevCond₂ h₂ p ↔
      ∀ k : S₂, 0 < ∑ j, p j k → ∀ r : S₂, condPayoff₂ h₂ p r k ≤ condPayoff₂ h₂ p k k) := by sorry

end Aumann1987.TwoPerson
