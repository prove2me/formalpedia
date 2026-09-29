-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_error_step_6_1
-- name    : ConjGrad.ErrorDecrease.error_step_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:55:49.627725+00:00
-- url     : https://prove2.me/theorems/362d4532-beb3-4ba1-9ad8-706e7586b843
-- title:
--   Theorem 6:1, eq. (6:1) — one cg step lowers $f$ by $a_i|r_i|^2=\mu(p_i)|x_i-x_{i+1}|^2$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k,x_0\in\mathbb{R}^n$, and let $h$ solve $Ah=k$. Let $x_i$, $r_i$, $p_i$, $a_i$ be the quantities of the cg-method (5:1) started at $x_0$, let $f(x)=(h-x,A(h-x))$ be the error function (4:5), and let $\mu(z)=(z,Az)/|z|^2$ be the Rayleigh quotient (4:12). Then for every $i\ge 0$, the step from $x_i$ to $x_{i+1}$ diminishes $f$ by the amount
--
--   $$
--   f(x_i) - f(x_{i+1}) = a_i\,|r_i|^2 = \mu(p_i)\,|x_i - x_{i+1}|^2 .
--   $$
--
--   This is (6:1) of the paper, whose step from $x_{i-1}$ to $x_i$ is written here with the index shifted by one. It shows that the error function decreases at every step of the cg-method, and summing it gives (6:2).
--
--   **Formalization Note** The statement is for all $i$, including steps after termination, where every term is $0$. The index is shifted (step $i+1$ goes from $x_i$ to $x_{i+1}$) to avoid natural-number subtraction.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 416, Theorem 6:1, eq. (6:1)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_step_6_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x)) := by sorry

end ConjGrad.ErrorDecrease
