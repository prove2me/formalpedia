-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_uRel_le_Ubound
-- name    : FeinbergLiang.ACOE.uRel_le_Ubound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:06:33.959071+00:00
-- url     : https://prove2.me/theorems/c7ff41af-5a44-46fe-b19c-8039cb3bd884
-- title:
--   Lemma 4.6 — the function $U$ of (4.13) is finite, locally bounded, integrable against the demand, and dominates every $u_\alpha$
-- statement:
--   Consider the inventory control problem. Let $[x^*_L,x^*_U]$ be a bounded interval with $\mathbb X_\alpha\subseteq[x^*_L,x^*_U]$ for all $\alpha\in[0,1)$, as in (4.4), and let $U$ be defined by (4.13):
--   $$U(x)=\begin{cases}K+\bar c(x^*_U-x), & x<x^*_L,\\ K+\bar c(x^*_U-x^*_L)+(E(x)+\bar c\,\mathbb E[D])(1+\mathbb E[N(x-x^*_L)]), & x\ge x^*_L.\end{cases}$$
--   Then:
--   1. $u_\alpha(x)\le U(x)<\infty$ for all $\alpha\in[0,1)$ and all $x\in\mathbb R$;
--   2. if $x_*\le x$, then $C(x_*,x):=\sup_{y\in[x_*,x]}U(y)<\infty$;
--   3. $\mathbb E[U(x-D)]<\infty$ for all $x\in\mathbb R$.
--
--   Items 1 and 3 give the dominating function required by Assumption EC(ii) for the inventory problem. Item 2 is used in the equicontinuity proof of Lemma 4.7.
--
--   **Formalization Note.** $U$ is $[0,\infty]$-valued by definition, and its finiteness is part of the conclusion. The expectation in item 3 is a lower Lebesgue integral against the demand law.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 579, Lemma 4.6, Eq. (4.13)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Lemma 4.6 (Feinberg–Liang 2022, p. 579). For an interval `[x*_L, x*_U]` satisfying (4.4) and
`U` defined by (4.13): (i) `u_α(x) ≤ U(x) < ∞` for all `α ∈ [0, 1)` and `x`;
(ii) `C(x_*, x) = sup_{y ∈ [x_*, x]} U(y) < ∞` for `x_* ≤ x`; (iii) `E[U(x - D)] < ∞`. -/
theorem uRel_le_Ubound (D : InventoryData) (xL xU : ℝ) (hLU : xL ≤ xU)
    (hI : ∀ α ∈ Set.Ico (0 : ℝ) 1, optSet (inventoryMDP D) α ⊆ Set.Icc xL xU) :
    ((∀ α ∈ Set.Ico (0 : ℝ) 1, ∀ x, uRel (inventoryMDP D) α x ≤ Ubound D xL xU x) ∧
      ∀ x, Ubound D xL xU x ≠ ⊤) ∧
    (∀ xs x : ℝ, xs ≤ x → (⨆ y ∈ Set.Icc xs x, Ubound D xL xU y) ≠ ⊤) ∧
    ∀ x, ∫⁻ d, Ubound D xL xU (x - d) ∂D.μ ≠ ⊤ := by sorry

end FeinbergLiang.ACOE
