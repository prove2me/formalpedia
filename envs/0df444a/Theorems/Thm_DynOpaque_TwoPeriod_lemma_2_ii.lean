-- Prove2me | Theorems.Thm_DynOpaque_TwoPeriod_lemma_2_ii
-- name    : DynOpaque.TwoPeriod.lemma_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:21.31227+00:00
-- url     : https://prove2.me/theorems/65215318-2cc9-4a86-97ca-e36835f1a058
-- title:
--   Lemma 2 (ii), p. 12 — optimal offering probabilities at p1 = p2 = vHL for (√17 − 3)/2 ≤ α < 1
-- statement:
--   Assume $v_H>v_L$, $c_H>c_L$, $c_L\le v_L$, and $\frac{\sqrt{17}-3}{2}\le\alpha<1$. Let $v_{HL}=\frac{v_H-v_L}{2}+v_L$ and $r=\frac{v_{HL}-c_L}{c_H-c_L}$, and consider objective (3), the profit at $p_1=p_2=v_{HL}$, over $(\xi_1,\xi_2)\in[0,1]^2$. Then:
--
--   1. if $r<\frac{2}{1+\alpha}$, an optimal decision is
--   $$
--   \xi_1=\frac{(1+\alpha)(v_{HL}-c_L)}{2(c_H-c_L)},\qquad \xi_2=0;
--   $$
--   2. if $\frac{2}{1+\alpha}\le r\le\frac{\alpha}{1-\alpha}$, an optimal decision is $\xi_1=1$, $\xi_2=0$;
--   3. if $\frac{\alpha}{1-\alpha}<r<\frac{2-\alpha}{1-\alpha}$, an optimal decision is $\xi_1=1$ and $\xi_2=\frac{(1-\alpha)(v_{HL}-c_L)-\alpha(c_H-c_L)}{2(1-\alpha)(c_H-c_L)}$;
--   4. if $r\ge\frac{2-\alpha}{1-\alpha}$, an optimal decision is $\xi_1=\xi_2=1$.
--
--   "Optimal" means that the stated pair lies in $[0,1]^2$ and maximizes (3) over $[0,1]^2$; uniqueness is not claimed. When most period-2 anecdotes come from period 1, the firm offers only $L$ in period 2 unless margins are large.
--
--   **Formalization Note** The page prints the fourth case as $(2-a)/(1-a)$; $a$ is a typo for $\alpha$. The range $\alpha<1$ is as printed (the middle cases divide by $1-\alpha$).
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, p. 12, Lemma 2 (ii)

import Mathlib
import Definitions.Def_DynOpaque_TwoPeriod_Model

namespace DynOpaque.TwoPeriod

/-- Lemma 2 (ii), p. 12: optimal offering decisions for objective (3) (`p₁ = p₂ = vHL`) when
`(√17 − 3)/2 ≤ α < 1`, in four regimes of the ratio `(vHL − cL)/(cH − cL)`. -/
theorem lemma_2_ii (vH vL cH cL α : ℝ) (hS : Standing vH vL cH cL α) (hα : alphaBar ≤ α)
    (hα1 : α < 1) :
    ((vHL vH vL - cL) / (cH - cL) < 2 / (1 + α) →
      IsOptimalOffering (obj3 vH vL cH cL α)
        ((1 + α) * (vHL vH vL - cL) / (2 * (cH - cL))) 0) ∧
    (2 / (1 + α) ≤ (vHL vH vL - cL) / (cH - cL) →
      (vHL vH vL - cL) / (cH - cL) ≤ α / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1 0) ∧
    (α / (1 - α) < (vHL vH vL - cL) / (cH - cL) →
      (vHL vH vL - cL) / (cH - cL) < (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1
        (((1 - α) * (vHL vH vL - cL) - α * (cH - cL)) / (2 * (1 - α) * (cH - cL)))) ∧
    ((vHL vH vL - cL) / (cH - cL) ≥ (2 - α) / (1 - α) →
      IsOptimalOffering (obj3 vH vL cH cL α) 1 1) := by sorry

end DynOpaque.TwoPeriod
