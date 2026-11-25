-- Prove2me | Theorems.Thm_Arxiv1007_0377_index_quartic
-- name    : Arxiv1007_0377.index_quartic
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T00:00:12.260912+00:00
-- url     : https://prove2.me/theorems/4a4fc1f1-aec0-4c5d-afc7-2c6ee5d4afe1
-- title:
--   Eq. (1): the quartic for the real part of the refractive index
-- statement:
--   Let $\epsilon=\epsilon_r+i\epsilon_i$ and $\mu=\mu_r+i\mu_i$ be complex numbers. Write $A=\epsilon_r\mu_r-\epsilon_i\mu_i$ and $B=\epsilon_r\mu_i+\epsilon_i\mu_r$.
--
--   1. If $n,\kappa\in\mathbb{R}$ and $N=n+i\kappa$ satisfies $N^2=\epsilon\mu$, then
--
--   $$n^4-\left(\frac{\epsilon_r\mu_i+\epsilon_i\mu_r}{2}\right)^2-(\epsilon_r\mu_r-\epsilon_i\mu_i)\,n^2=0,$$
--
--   and $\kappa$ satisfies the similar quartic $\kappa^4+A\kappa^2-(B/2)^2=0$.
--   2. The four roots of the quartic $X^4-(B/2)^2-AX^2$ in $\mathbb{C}$ are two real numbers $\pm a$ and two purely imaginary numbers $\pm ib$, $a,b\in\mathbb{R}$:
--
--   $$X^4-\left(\tfrac{B}{2}\right)^2-AX^2=(X-a)(X+a)(X-ib)(X+ib).$$
--
--   This is the equation from which the paper reads off the possible values of the real part $n$ of the refractive index.
--
--   **Formalization Note** The paper says only that "a similar equation exists for $\kappa$". The statement gives that equation explicitly. The claim that two roots are real and two purely imaginary is stated as a factorization. Roots are counted with multiplicity, so when $B=0$ and $A\ge0$ the pair $\pm ib$ is $0,0$.
-- source:
--   Hickey, Akyurtlu and Kussow, Relationship between the Kramers-Kronig relations and negative index of refraction, arXiv:1007.0377v2 (2010), claim c001; main text (no sections), eq. (1) and the sentence after it, PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem index_quartic (ε μ : ℂ) :
    (∀ n κ : ℝ, ((n : ℂ) + κ * I) ^ 2 = ε * μ →
      (indexQuartic ε μ).eval (n : ℂ) = 0 ∧
      κ ^ 4 + epsMuRe ε μ * κ ^ 2 - (epsMuIm ε μ / 2) ^ 2 = 0) ∧
    ∃ a b : ℝ, indexQuartic ε μ =
      (X - C (a : ℂ)) * (X + C (a : ℂ)) * (X - C ((b : ℂ) * I)) * (X + C ((b : ℂ) * I)) := by sorry

end Arxiv1007_0377
