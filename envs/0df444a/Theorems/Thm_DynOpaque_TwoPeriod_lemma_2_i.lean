-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_2_i
-- name    : DynOpaque.TwoPeriod.lemma_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:18.945655+00:00
-- url     : https://prove2.me/theorems/14070d6f-f397-4245-8f9a-7ab6ca007636
-- title:
--   Lemma 2 (i), p. 12 — optimal offering probabilities at p1 = p2 = vHL for 0 ≤ α < (√17 − 3)/2
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $0\le\alpha\le1$, $c_L\le v_L$, and $\alpha<\frac{\sqrt{17}-3}{2}$. Let $v_{HL}=\frac{v_H-v_L}{2}+v_L$, write $r=\frac{v_{HL}-c_L}{c_H-c_L}$, and consider objective (3), the profit at $p_1=p_2=v_{HL}$, over $(\xi_1,\xi_2)\in[0,1]^2$. Then:
--
--   1. if $r<\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}$, an optimal decision is
--   $$
--   \xi_1=\frac{(2-\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)},\qquad \xi_2=\frac{(2-3\alpha-\alpha^2)(v_{HL}-c_L)}{(4-4\alpha-\alpha^2)(c_H-c_L)};
--   $$
--   2. if $\frac{4-4\alpha-\alpha^2}{2-\alpha-\alpha^2}\le r<\frac{2-\alpha}{1-\alpha}$, an optimal decision is $\xi_1=1$ and $\xi_2=\frac{(1-\alpha)(v_{HL}-c_L)-\alpha(c_H-c_L)}{2(1-\alpha)(c_H-c_L)}$;
--   3. if $r\ge\frac{2-\alpha}{1-\alpha}$, an optimal decision is $\xi_1=\xi_2=1$.
--
--   "Optimal" means that the stated pair lies in $[0,1]^2$ and maximizes (3) over $[0,1]^2$; uniqueness is not claimed. When few period-2 anecdotes come from period 1, the firm offers $H$ with a higher probability early on and a lower one later.
--
--   **Formalization Note** The page prints the third case as $(2-a)/(1-a)$; $a$ is a typo for $\alpha$. All divisions are well defined: $c_H>c_L$ and, for $\alpha<\frac{\sqrt{17}-3}{2}<1$, $2-\alpha-\alpha^2>0$, $4-4\alpha-\alpha^2>0$, $1-\alpha>0$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 12, Lemma 2 (i)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Lemma 2 (i), p. 12: optimal offering decisions for objective (3) (`p₁ = p₂ = vHL`) when
`0 ≤ α < (√17 − 3)/2`, in three regimes of the ratio `(vHL − cL)/(cH − cL)`. -/
theorem lemma_2_i (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (hα : α < alphaBar) :
    ((vHL vH vL - cL) / (cH - cL) < (4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) →
      IsOptimalOffering (obj3 vH vL cH cL α)
        ((2 - α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))
        ((2 - 3 * α - α ^ 2) * (vHL vH vL - cL) / ((4 - 4 * α - α ^ 2) * (cH - cL)))) ∧
    ((4 - 4 * α - α ^ 2) / (2 - α - α ^ 2) ≤ (vHL vH vL - cL) / (cH - cL) →
      (vHL vH vL - cL) / (cH - cL) < (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1
        (((1 - α) * (vHL vH vL - cL) - α * (cH - cL)) / (2 * (1 - α) * (cH - cL)))) ∧
    ((vHL vH vL - cL) / (cH - cL) ≥ (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1 1) := by sorry

end DynOpaque.TwoPeriod
