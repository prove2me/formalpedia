-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_5
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:58:53.157027+00:00
-- url     : https://prove2.me/theorems/fd60954e-87f1-4264-bd46-5c3a352f24bb
-- title:
--   Theorem 6:5 — the point (6:8) of $P_i$ nearest to $h$, beyond $x_i$, with (6:9) and (6:10)
-- statement:
--   Let $x_0,\dots,x_m=h$ be the cg estimates for a real symmetric positive definite $A$, $f(x)=(h-x,A(h-x))$ and $\mu$ the Rayleigh quotient. Fix $1\le i<m$. The point
--
--   $$x_m^{(i)}=x_i+\frac{f(x_i)}{|r_{i-1}|^2}\,p_{i-1} \tag{6:8}$$
--
--   is the point of $P_i$ whose distance from $h$ is the least (every other point of $P_i$ is strictly farther). It lies on the line $x_{i-1}x_i$ beyond $x_i$: $x_m^{(i)}=x_{i-1}+t(x_i-x_{i-1})$ with $t>1$. Moreover
--
--   $$\frac1{f(x_m^{(i)})}=\frac1{f(x_i)}-\frac1{f(x_{i-1})}, \tag{6:9}$$
--
--   $$|h-x_i|^2=|h-x_m^{(i)}|^2+\frac{f(x_m^{(i)})-f(x_i)}{\mu(p_{i-1})}. \tag{6:10}$$
--
--   The point $x_m^{(i)}$ is the improved estimate available when the algorithm is stopped before its final step.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: the theorem for an index $i$ → $1\le i<m$; reason: the statement needs $x_{i-1}$; the preceding paragraph places it before the final step, and at $i=m$ the reciprocals in (6:9) are undefined
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 417, Theorem 6:5, eqs. (6:8)–(6:10) (PDF p. 9)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:5 (Hestenes–Stiefel 1952, p. 417), at the paper's index `i = j + 1` with
`1 ≤ i < m`: the point `xₘ⁽ⁱ⁾ = xᵢ + (f(xᵢ)/|r_{i−1}|²) p_{i−1}` (6:8) is the unique nearest
point of `Pᵢ` to `h`, lies on the line `x_{i−1}xᵢ` beyond `xᵢ`, and satisfies (6:9), (6:10). -/
theorem theorem_6_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) (j : ℕ) (hj : j + 1 < m) :
    (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p ∈
      cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1) ∧
    (∀ z ∈ cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1),
      z ≠ (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p →
      (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) ⬝ᵥ
        (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) <
      (h - z) ⬝ᵥ (h - z)) ∧
    (∃ t : ℝ, 1 < t ∧
      (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p =
        (cgIter A k x₀ j).x + t • ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x)) ∧
    1 / errorFun A h ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p) =
      1 / errorFun A h (cgIter A k x₀ (j + 1)).x - 1 / errorFun A h (cgIter A k x₀ j).x ∧
    (h - (cgIter A k x₀ (j + 1)).x) ⬝ᵥ (h - (cgIter A k x₀ (j + 1)).x) =
      (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) ⬝ᵥ
        (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) +
      (errorFun A h ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p) -
        errorFun A h (cgIter A k x₀ (j + 1)).x) / rayleigh A (cgIter A k x₀ j).p := by sorry

end ConjGrad.ErrorDecrease.Supplement
