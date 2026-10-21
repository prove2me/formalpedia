-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_eq_23
-- name    : CommittedLiquidity.BreakEven.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.400285+00:00
-- url     : https://prove2.me/theorems/1050d59f-894a-43f1-b6bb-0a8ba54b791e
-- title:
--   Equation (23), p. 27 — regulator payoff rearranged using buyers’ profit
-- statement:
--   For a committed price $P\in[\underline P,qD_2]$, write $u_s(P)=\Pr(\theta<\theta^*(P)\mid s)$, let $p_s$ be the prior of state $s\in\{G,B\}$, and let $\Pi_M(P)$ be the buyers' profit conditional on $M$ runs. Then the regulator's expected payoff from (22) satisfies
--
--   $$V_A(P)=\sum_{M=1}^{2}\left(\sum_{s\in\{G,B\}}p_su_s(P)^M(1-u_s(P))^{2-M}\right){2\choose M}M\frac{D_1}{P}\Pi_M(P).$$
--
--   This identity relates the regulator's ex ante payoff to the two market break-even conditions.
--
--   **Formalization Note** $V_A$ remains defined by (22); this theorem asserts the nontrivial rearrangement (23). The uniform tail probability is $1-u_s(P)$ because the distribution is continuous.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 27 (PDF 28), equation (23)

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem eq_23 (p : Params) (hp : p.Standing) (P : ℝ)
    (hP : P ∈ Set.Icc p.Plow (p.q * p.D2)) :
    p.VA P = ∑ M ∈ Finset.Icc 1 2,
      (∑ s : State,
        p.prior s * p.probBelow s (p.θstar P) ^ M *
          (1 - p.probBelow s (p.θstar P)) ^ (2 - M)) *
        (Nat.choose 2 M : ℝ) * (M : ℝ) * (p.D1 / P) * p.Pi M P := by sorry
end CommittedLiquidity.BreakEven
