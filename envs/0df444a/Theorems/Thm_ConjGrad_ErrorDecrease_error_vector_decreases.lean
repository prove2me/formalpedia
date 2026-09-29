-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_error_vector_decreases
-- name    : ConjGrad.ErrorDecrease.error_vector_decreases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:57:36.622857+00:00
-- url     : https://prove2.me/theorems/dbe3301a-b10e-4579-afa8-935b43b3240c
-- title:
--   Theorem 6:3 — each cg step shortens the error vector, with the exact decrease (6:5)
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k\in\mathbb{R}^n$, and let $h$ be the solution of $Ah=k$. Run the cg-method (5:1) from an arbitrary starting point $x_0$, producing estimates $x_i$, residuals $r_i$ and direction vectors $p_i$. Write $y_i=h-x_i$ for the error vector of $x_i$, $f(x)=(h-x,A(h-x))$ for the error function (4:5) and $\mu(z)=(z,Az)/|z|^2$ for the Rayleigh quotient (4:12).
--
--   For every index $i$ with $r_i\neq 0$ (that is, every step $x_i\to x_{i+1}$ that the algorithm actually performs), the step reduces the Euclidean length of the error vector, and the reduction is exactly
--
--   $$
--   |y_i|^2 - |y_{i+1}|^2 = \frac{f(x_{i+1}) + f(x_i)}{\mu(p_i)}, \qquad\text{and}\qquad |y_{i+1}| < |y_i| .
--   $$
--
--   This is Theorem 6:3 of Hestenes and Stiefel, whose step from $x_{i-1}$ to $x_i$ is written here with the index shifted by one. The cg-method minimizes the $A$-weighted error $f$, not the Euclidean error; the theorem shows that the Euclidean distance $|h-x_i|$ to the solution also decreases strictly at every step, although the residual $|r_i|$ need not. This justifies stopping the algorithm before the final step.
--
--   **Formalization Note** The hypothesis $r_i\neq 0$ says that step $i+1$ takes place (the paper's range $i\le m$); it is needed, since after termination both sides of the identity are $0$ and the strict inequality fails. Termination itself ($x_m=h$ for some $m\le n$) is not assumed. The strict decrease is stated for the squared lengths $(y,y)$, which is equivalent because lengths are nonnegative.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 416, Theorem 6:3, eq. (6:5)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_vector_decreases {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i : ℕ) (hr : (cgIter A k x₀ i).r ≠ 0) :
    (h - (cgIter A k x₀ i).x) ⬝ᵥ (h - (cgIter A k x₀ i).x) -
        (h - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ (h - (cgIter A k x₀ (i + 1)).x) =
      (errorFun A h (cgIter A k x₀ (i + 1)).x + errorFun A h (cgIter A k x₀ i).x) /
        rayleigh A (cgIter A k x₀ i).p ∧
    (h - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ (h - (cgIter A k x₀ (i + 1)).x) <
      (h - (cgIter A k x₀ i).x) ⬝ᵥ (h - (cgIter A k x₀ i).x) := by sorry

end ConjGrad.ErrorDecrease
