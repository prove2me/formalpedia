-- Prove2me | Theorems.Thm_Arxiv1007_0377_real_branches_formula
-- name    : Arxiv1007_0377.real_branches_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:00:54.533609+00:00
-- url     : https://prove2.me/theorems/05c4c579-5d0e-4f60-8b71-69989cd0804c
-- title:
--   Eq. (2): the two real solution branches $n_\pm$
-- statement:
--   Let $\epsilon=\epsilon_r+i\epsilon_i$ and $\mu=\mu_r+i\mu_i$ be complex numbers. Let $A=\epsilon_r\mu_r-\epsilon_i\mu_i$ and $B=\epsilon_r\mu_i+\epsilon_i\mu_r$, and let
--
--   $$n_\pm=\pm\frac{\sqrt{\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|}}{\sqrt2}.$$
--
--   Then:
--
--   1. the radicand is non-negative: $\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|\ge0$;
--   2. $n_+$ and $n_-$ are the two real roots of the quartic (1), and the remaining two are purely imaginary:
--
--   $$X^4-\left(\tfrac{B}{2}\right)^2-AX^2=(X-n_+)(X-n_-)(X-im)(X+im),\qquad m=\frac{\sqrt{|\epsilon||\mu|-(\epsilon_r\mu_r-\epsilon_i\mu_i)}}{\sqrt2};$$
--   3. every $N\in\mathbb{C}$ with $N^2=\epsilon\mu$ has real part $n_+$ or $n_-$;
--   4. both values occur: there are square roots $N$ of $\epsilon\mu$ with $\operatorname{Re}N=n_+$ and with $\operatorname{Re}N=n_-$.
--
--   Thus $n_+\ge0$ and $n_-=-n_+$ are the two candidate values of the real refractive index $n=\operatorname{Re}N$.
--
--   **Formalization Note** The paper writes only the formula for $n_\pm$. Items 2 to 4 make precise what "the two real solutions" means: they are the real roots of (1) and the possible real parts of $N$.
-- source:
--   Hickey, Akyurtlu and Kussow, Relationship between the Kramers-Kronig relations and negative index of refraction, arXiv:1007.0377v2 (2010), claim c002; main text, eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem real_branches_formula (ε μ : ℂ) :
    0 ≤ branchRadicand ε μ ∧
    indexQuartic ε μ =
      (X - C ((nPlus ε μ : ℝ) : ℂ)) * (X - C ((nMinus ε μ : ℝ) : ℂ)) *
        (X - C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) *
        (X + C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) ∧
    (∀ N : ℂ, N ^ 2 = ε * μ → N.re = nPlus ε μ ∨ N.re = nMinus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nPlus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nMinus ε μ) := by sorry

end Arxiv1007_0377
