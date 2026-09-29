-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_error_diff_6_2
-- name    : ConjGrad.ErrorDecrease.error_diff_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:56:26.470447+00:00
-- url     : https://prove2.me/theorems/4a142e6a-f0ee-4331-be9a-8e85068c24db
-- title:
--   Theorem 6:1, eq. (6:2) — $f(x_i)-f(x_j)=a_i|r_i|^2+\cdots+a_{j-1}|r_{j-1}|^2$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, let $k,x_0\in\mathbb{R}^n$, and let $h$ solve $Ah=k$. Let $x_l$, $r_l$ and $a_l$ be the estimates, residuals and step lengths of the cg-method (5:1) started at $x_0$, and let $f(x)=(h-x,A(h-x))$ be the error function (4:5). Then for all indices $i<j$,
--
--   $$
--   f(x_i) - f(x_j) = a_i|r_i|^2 + a_{i+1}|r_{i+1}|^2 + \cdots + a_{j-1}|r_{j-1}|^2 = \sum_{l=i}^{j-1} a_l\,|r_l|^2 .
--   $$
--
--   The identity gives the total decrease of the error function over several steps of the method. With $j=m$ and $x_m=h$, it expresses $f(x_i)$ itself as a sum of computable quantities, which is how it enters the proof of Theorem 6:3.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 416, Theorem 6:1, eq. (6:2)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease

theorem error_diff_6_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (i j : ℕ) (hij : i < j) :
    errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ j).x =
      ∑ l ∈ Finset.Ico i j,
        cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r) := by sorry

end ConjGrad.ErrorDecrease
