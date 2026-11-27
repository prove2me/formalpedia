-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_4
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:58:17.724832+00:00
-- url     : https://prove2.me/theorems/2fd933c2-3fcc-4d8b-8e05-4c7f39528698
-- title:
--   Theorem 6:4 (corrected: base point in (6:7b)) — ordered Euclidean projections on the CG planes
-- statement:
--   Let $x_0,\dots,x_m=h$ be the cg estimates for a real symmetric positive definite $A$ and $f(x)=(h-x,A(h-x))$. Fix $1\le i<m$ and let $x_k^{(i)}$ ($i<k\le m$) be the orthogonal projection of $x_k$ on the plane $P_i$ through $x_0,\dots,x_i$. Then
--
--   $$x_k^{(i)}=x_{i-1}+t_k(x_i-x_{i-1}),\quad t_k=\frac{f(x_{i-1})-f(x_k)}{f(x_{i-1})-f(x_i)}, \tag{6:7a}$$
--
--   $$x_k^{(i)}=x_i+\frac{f(x_i)-f(x_k)}{|r_{i-1}|^2}\,p_{i-1}, \tag{6:7b}$$
--
--   and the points $x_{i-1},x_i,x_{i+1}^{(i)},\dots,x_m^{(i)}$ lie on a straight line in this order: $x_i\ne x_{i-1}$ and $0<1<t_{i+1}<\cdots<t_m$.
--
--   The projections show how stopping early can be improved: all later estimates project onto the single line through the last two estimates (§6, preceding paragraph).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - correction: (6:7b) $x_k^{(i)}=x_{i-1}+\frac{f(x_i)-f(x_k)}{|r_{i-1}|^2}p_{i-1}$ → base point $x_i$ instead of $x_{i-1}$; reason: typo: the printed formula contradicts (6:7a) (since $x_i-x_{i-1}=a_{i-1}p_{i-1}$ and $f(x_{i-1})-f(x_i)=a_{i-1}|r_{i-1}|^2$) and (6:8) at $k=m$; e.g. at $k=m$ the printed point differs from the projection by $a_{i-1}p_{i-1}\ne0$. See DISPROOF.md
--   - reading: the theorem for an index $i$ with projections of $x_{i+1},\dots,x_m$ → $1\le i<m$; reason: the statement needs $x_{i-1}$ and is empty for $i=m$; the preceding paragraph places it before the final step
--   - encoding: the projection $x_k^{(i)}$ → the point of $P_i$ with $x_k-x_k^{(i)}$ orthogonal to all of $P_i$ (Euclidean); reason: the defining property of the orthogonal projection on an affine plane
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 417, Theorem 6:4, eqs. (6:7a), (6:7b) (PDF p. 9)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:4 (Hestenes–Stiefel 1952, p. 417), corrected (6:7b), at the paper's index
`i = j + 1` with `1 ≤ i < m`: the Euclidean projection of `xₖ` (`i < k ≤ m`) on the plane `Pᵢ`
is the point `x_{i−1} + tₖ(xᵢ − x_{i−1})` of (6:7a), also given by (6:7b) with base point `xᵢ`,
and `0 = t_{i−1} < 1 = tᵢ < t_{i+1} < ⋯ < tₘ`. -/
theorem theorem_6_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) (j : ℕ) (hj : j + 1 < m) :
    (cgIter A k x₀ (j + 1)).x ≠ (cgIter A k x₀ j).x ∧
    (∀ kk : ℕ, j + 1 < kk → kk ≤ m →
      (cgIter A k x₀ j).x +
          ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk).x) /
            (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x)) •
          ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x) ∈
        cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1) ∧
      (∀ z ∈ cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1),
        ((cgIter A k x₀ kk).x - ((cgIter A k x₀ j).x +
          ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk).x) /
            (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x)) •
          ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x))) ⬝ᵥ
        (z - ((cgIter A k x₀ j).x +
          ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk).x) /
            (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x)) •
          ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x))) = 0) ∧
      (cgIter A k x₀ j).x +
          ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk).x) /
            (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x)) •
          ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x) =
        (cgIter A k x₀ (j + 1)).x +
          ((errorFun A h (cgIter A k x₀ (j + 1)).x - errorFun A h (cgIter A k x₀ kk).x) /
            ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p) ∧
    1 < (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 2)).x) /
      (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x) ∧
    (∀ kk kk' : ℕ, j + 1 < kk → kk < kk' → kk' ≤ m →
      (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk).x) /
          (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x) <
        (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ kk').x) /
          (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x)) := by sorry

end ConjGrad.ErrorDecrease.Supplement
