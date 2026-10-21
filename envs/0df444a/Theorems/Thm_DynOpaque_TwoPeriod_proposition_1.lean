-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_proposition_1
-- name    : DynOpaque.TwoPeriod.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:40.012084+00:00
-- url     : https://prove2.me/theorems/b5514ff6-efa6-42e2-a019-2f05a6162672
-- title:
--   Proposition 1, p. 13 — with one anecdote, the optimal two-period policy: probabilistic selling at vHL with ξ1* > ξ2*, or transparent selling
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$. Let $v_{HL}=\frac{v_H-v_L}{2}+v_L$, $\bar\alpha=\frac{\sqrt{17}-3}{2}$, and $M=\max\{v_H-c_H,\ v_L-c_L\}$. Each customer draws one anecdote ($K=1$). Optimality is over all feasible policies: opaque policies with any prices $p_1,p_2\le v_{HL}$ and any offering probabilities $\xi_1,\xi_2\in[0,1]$, and transparent single-version policies with any prices.
--
--   1. If $0\le\alpha<\bar\alpha$, $\frac{v_{HL}-c_L}{c_H-c_L}<\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}$ and $\frac{(1-\alpha)(v_{HL}-c_L)^2}{(4-4\alpha-\alpha^2)(c_H-c_L)}>M$, it is optimal to sell probabilistically with
--   $$
--   p_1^*=p_2^*=v_{HL},\quad \xi_1^*=\frac{(2-\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)},\quad \xi_2^*=\frac{(2-3\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)},\quad \Pi^*=\frac{2(1-\alpha)(v_{HL}-c_L)^2}{(4-4\alpha-\alpha^2)(c_H-c_L)}.
--   $$
--   2. If $\bar\alpha\le\alpha\le1$, $\frac{v_{HL}-c_L}{c_H-c_L}<\frac{2}{1+\alpha}$ and $\frac{(1+\alpha)^2(v_{HL}-c_L)^2}{8(c_H-c_L)}>M$, it is optimal to sell probabilistically with
--   $$
--   p_1^*=p_2^*=v_{HL},\quad \xi_1^*=\frac{(1+\alpha)(v_{HL}-c_L)}{2(c_H-c_L)},\quad \xi_2^*=0,\quad \Pi^*=\frac{(1+\alpha)^2(v_{HL}-c_L)^2}{4(c_H-c_L)}.
--   $$
--   3. Otherwise (neither the hypotheses of 1 nor those of 2 hold): if $v_H-c_H\ge v_L-c_L$, it is optimal to sell $H$ transparently at $p_1^*=p_2^*=v_H$, with $\Pi^*=2(v_H-c_H)$; if $v_L-c_L\ge v_H-c_H$, it is optimal to sell $L$ transparently at $p_1^*=p_2^*=v_L$, with $\Pi^*=2(v_L-c_L)$.
--
--   In each case "optimal" means that the policy is feasible and no feasible policy earns more, and the stated $\Pi^*$ is its profit. When both products have low transparent margins, the firm gains by randomizing which version it delivers, and it front-loads the high version so that early $H$ deliveries become favourable anecdotes for later customers.
--
--   **Formalization Note** Two assumptions are added to the page and disclosed: $c_L\le v_L$ (used in the paper's proof, p. 30) and the restriction of opaque prices to $p_t\le v_{HL}$ (the largest candidate price of Lemma 1; above it nobody buys and the paper's anecdote dynamics are undefined). Demand is computed from the anecdote estimate and the purchase rule, with equality buying. "Otherwise" in part 3 is the negation of the full hypothesis lists of parts 1 and 2.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 13, Proposition 1

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Proposition 1, p. 13: with one anecdote per customer (`K = 1`), the globally optimal selling
policy over all feasible opaque policies (prices `≤ vHL`, offering probabilities in `[0, 1]`) and
all transparent single-version policies. (i), (ii): probabilistic selling at `vHL` in both periods
with the printed `ξ₁*`, `ξ₂*`, `Π*`; (iii) otherwise, transparent selling of the version with the
larger margin. -/
theorem proposition_1 (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) :
    ((0 ≤ α ∧ α < alphaBar ∧
        (vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ∧
        (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) >
          max (vH - cH) (vL - cL)) →
      IsOptimal vH vL cH cL α
          (Policy.opaque (vHL vH vL) (vHL vH vL)
            ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
            ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) ∧
        profit vH vL cH cL α
            (Policy.opaque (vHL vH vL) (vHL vH vL)
              ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
              ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) =
          2 * (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL))) ∧
    ((alphaBar ≤ α ∧ α ≤ 1 ∧
        (vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) ∧
        (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL)) > max (vH - cH) (vL - cL)) →
      IsOptimal vH vL cH cL α
          (Policy.opaque (vHL vH vL) (vHL vH vL)
            ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
        profit vH vL cH cL α
            (Policy.opaque (vHL vH vL) (vHL vH vL)
              ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) =
          (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (4 * (cH - cL))) ∧
    (¬ (0 ≤ α ∧ α < alphaBar ∧
        (vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ∧
        (1 - α) * (vHL vH vL - cL) ^ 2 / ((4 - 4 * α - α ^ 2) * (cH - cL)) >
          max (vH - cH) (vL - cL)) →
      ¬ (alphaBar ≤ α ∧ α ≤ 1 ∧
        (vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) ∧
        (1 + α) ^ 2 * (vHL vH vL - cL) ^ 2 / (8 * (cH - cL)) > max (vH - cH) (vL - cL)) →
      (vH - cH ≥ vL - cL →
          IsOptimal vH vL cH cL α (Policy.transparent Version.H vH vH) ∧
            profit vH vL cH cL α (Policy.transparent Version.H vH vH) = 2 * (vH - cH)) ∧
        (vL - cL ≥ vH - cH →
          IsOptimal vH vL cH cL α (Policy.transparent Version.L vL vL) ∧
            profit vH vL cH cL α (Policy.transparent Version.L vL vL) = 2 * (vL - cL))) := by sorry

end DynOpaque.TwoPeriod
