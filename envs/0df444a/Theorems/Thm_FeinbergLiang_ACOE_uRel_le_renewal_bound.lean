-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_uRel_le_renewal_bound
-- name    : FeinbergLiang.ACOE.uRel_le_renewal_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:05:40.093976+00:00
-- url     : https://prove2.me/theorems/f16bbfbd-3945-4f92-aef4-0b526be45b0f
-- title:
--   Eqs. (4.11)–(4.12) — renewal-process upper bounds on the discounted relative value function $u_\alpha$
-- statement:
--   Consider the inventory control problem. Let $[x^*_L,x^*_U]$ be an interval with $\mathbb X_\alpha\subseteq[x^*_L,x^*_U]$ for all $\alpha\in[0,1)$, as in (4.4). Fix $\alpha\in[0,1)$ and a state $x_\alpha$ with $v_\alpha(x_\alpha)=m_\alpha$. Let $N(t)$ be the renewal process of the cumulative demands, and let $E(x)=h(x)+E_{x-x^*_L}(x)$ with $E_y(x)=\mathbb E[h(x-S_{N(y)+1})]$. Then
--   $$u_\alpha(x)\le K+\bar c(x^*_U-x)\quad\text{for } x<x_\alpha,\qquad(4.11)$$
--   $$u_\alpha(x)\le K+(E(x)+\bar c\,\mathbb E[D])(1+\mathbb E[N(x-x^*_L)])\quad\text{for } x\ge x_\alpha.\qquad(4.12)$$
--
--   The paper cites these bounds from Feinberg and Lewis (2015, inequalities (6.11), (6.17)). They are the input to Lemma 4.6.
--
--   **Formalization Note.** The paper describes $x_\alpha$ as "a state such that $u_\alpha(x_\alpha)=m_\alpha$", a misprint for $v_\alpha(x_\alpha)=m_\alpha$, i.e. $x_\alpha\in\mathbb X_\alpha$. The paper also writes $x^\alpha$ for the same point in (4.11)–(4.12). All quantities are in $[0,\infty]$, and $\mathbb E[D]$ and $\mathbb E[N(t)]$ are lower Lebesgue integrals.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 578, Eqs. (4.11), (4.12) (citing Feinberg and Lewis 2015, inequalities (6.11), (6.17))

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Eqs. (4.11)–(4.12) (Feinberg–Liang 2022, p. 578, citing Feinberg and Lewis 2015, inequalities
(6.11), (6.17)). Let `[x*_L, x*_U]` be an interval satisfying (4.4), `α ∈ [0, 1)`, and `x_α` a
minimizer of `v_α`. Then `u_α(x) ≤ K + c̄(x*_U - x)` for `x < x_α`, and
`u_α(x) ≤ K + (E(x) + c̄ E[D])(1 + E[N(x - x*_L)])` for `x ≥ x_α`. -/
theorem uRel_le_renewal_bound (D : InventoryData) (xL xU : ℝ) (hLU : xL ≤ xU)
    (hI : ∀ α ∈ Set.Ico (0 : ℝ) 1, optSet (inventoryMDP D) α ⊆ Set.Icc xL xU)
    (α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1) (xα : ℝ) (hxα : xα ∈ optSet (inventoryMDP D) α) :
    (∀ x, x < xα → uRel (inventoryMDP D) α x ≤ ENNReal.ofReal (D.K + D.cbar * (xU - x))) ∧
    (∀ x, xα ≤ x → uRel (inventoryMDP D) α x ≤
      ENNReal.ofReal D.K +
        (Efun D xL x + ENNReal.ofReal D.cbar * meanDemand D) * (1 + meanRenewal D (x - xL))) := by sorry

end FeinbergLiang.ACOE
