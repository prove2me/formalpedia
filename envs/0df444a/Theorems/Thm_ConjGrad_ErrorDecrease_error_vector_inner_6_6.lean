-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_error_vector_inner_6_6
-- name    : ConjGrad.ErrorDecrease.error_vector_inner_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:56:56.229658+00:00
-- url     : https://prove2.me/theorems/0f27c593-1d38-44b0-82ea-4420ab2b8568
-- title:
--   Section 6, eq. (6:6) — $(y_{i+1},x_{i+1}-x_i)=f(x_{i+1})/\mu(p_i)$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k,x_0\in\mathbb{R}^n$, and let $h$ solve $Ah=k$. Let $x_i$ and $p_i$ be the estimates and direction vectors of the cg-method (5:1) started at $x_0$, write $y_i=h-x_i$ for the error vector of $x_i$, let $f(x)=(h-x,A(h-x))$ be the error function (4:5), and let $\mu(z)=(z,Az)/|z|^2$ be the Rayleigh quotient (4:12). Then for every $i\ge 0$,
--
--   $$
--   (y_{i+1},\,x_{i+1}-x_i) = \frac{f(x_{i+1})}{\mu(p_i)} .
--   $$
--
--   This is the identity (6:6), displayed in the paper's proof of Theorem 6:3 (with the index shifted by one): the step $x_{i+1}-x_i$ and the new error vector $y_{i+1}$ make a nonnegative inner product, whose value is determined by the error function. It is the ingredient that turns the decrease of $f$ into a decrease of the Euclidean length of the error vector.
--
--   **Formalization Note** The statement is for all $i$, including steps after termination; there $x_{i+1}=x_i=h$ and both sides are $0$. The index is shifted (step $i+1$ goes from $x_i$ to $x_{i+1}$) to avoid natural-number subtraction.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 417, Section 6, eq. (6:6) (in the proof of Theorem 6:3)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_vector_inner_6_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) :
    (h - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ ((cgIter A k x₀ (i + 1)).x - (cgIter A k x₀ i).x) =
      errorFun A h (cgIter A k x₀ (i + 1)).x / rayleigh A (cgIter A k x₀ i).p := by sorry

end ConjGrad.ErrorDecrease
