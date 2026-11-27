-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_7_1
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:00:26.45772+00:00
-- url     : https://prove2.me/theorems/0eb45f86-cc80-4c53-8bc3-3068aa3a6196
-- title:
--   Theorem 7:1 — $p_i=c_i(k-A\bar x_i)$ and the closed forms (7:3)
-- statement:
--   Let $x_i,r_i,p_i,b_i$ be the cg quantities for a real symmetric positive definite $A$, and $c_i,\bar x_i$ the weights and smoothed estimates of (7:2): $c_0=1$, $c_{i+1}=1+b_ic_i$, $\bar x_0=x_0$, $\bar x_{i+1}=(x_{i+1}+b_ic_i\bar x_i)/c_{i+1}$. Then
--
--   $$p_i=c_i(k-A\bar x_i) \tag{7:1}$$
--
--   for every $i$, and for $i<m$
--
--   $$c_i=|r_i|^2\sum_{j=0}^i\frac1{|r_j|^2}=\frac{|p_i|^2}{|r_i|^2},\qquad \bar x_i=\frac{|r_i|^2}{c_i}\sum_{j=0}^i\frac{x_j}{|r_j|^2}, \tag{7:3a, 7:3b}$$
--
--   $$\bar r_i=k-A\bar x_i=\frac1{c_i}p_i=\frac{|r_i|^2}{c_i}\sum_{j=0}^i\frac{r_j}{|r_j|^2}, \tag{7:3c}$$
--
--   the middle equality of (7:3c) holding for every $i$. The coefficients of $x_0,\dots,x_i$ in (7:3b) (and of $r_0,\dots,r_i$ in (7:3c)) sum to one.
--
--   The smoothed estimates are weighted averages of the cg estimates whose residuals are the normalized conjugate gradients.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - reading: (7:3a)–(7:3c) and the unit sum, stated without range → the reciprocal-residual forms for $i<m$; (7:1) and $\bar r_i=p_i/c_i$ for every $i$; reason: at $i=m$ the reciprocal $1/|r_m|^2$ is undefined; the recursion gives $\bar x_m=h$, $\bar r_m=0$
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 418, Theorem 7:1, eqs. (7:1)–(7:3c) (PDF p. 10)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:1 (Hestenes–Stiefel 1952, p. 418): `pᵢ = cᵢ(k − Ax̄ᵢ)` (7:1) for `cᵢ`, `x̄ᵢ` given by
(7:2), and the closed forms (7:3a)–(7:3c) with coefficients summing to one before termination;
`m` is the step at which the cg-method terminates. -/
theorem theorem_7_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, (cgIter A k x₀ i).p = smoothC A k x₀ i • (k - A *ᵥ smoothX A k x₀ i)) ∧
    (smoothC A k x₀ 0 = 1 ∧ smoothX A k x₀ 0 = x₀ ∧
      ∀ i : ℕ, smoothC A k x₀ (i + 1) = 1 + cgBeta A k x₀ i * smoothC A k x₀ i ∧
        smoothX A k x₀ (i + 1) = (1 / smoothC A k x₀ (i + 1)) •
          ((cgIter A k x₀ (i + 1)).x + (cgBeta A k x₀ i * smoothC A k x₀ i) • smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i < m →
      smoothC A k x₀ i = ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) *
          ∑ j ∈ Finset.range (i + 1), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) ∧
        smoothC A k x₀ i = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r)) ∧
    (∀ i : ℕ, i < m →
      smoothX A k x₀ i = (((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i) •
        ∑ j ∈ Finset.range (i + 1),
          (1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).x) ∧
    (∀ i : ℕ, k - A *ᵥ smoothX A k x₀ i = (1 / smoothC A k x₀ i) • (cgIter A k x₀ i).p) ∧
    (∀ i : ℕ, i < m →
      k - A *ᵥ smoothX A k x₀ i =
        (((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i) •
          ∑ j ∈ Finset.range (i + 1),
            (1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).r) ∧
    (∀ i : ℕ, i < m →
      ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i *
        ∑ j ∈ Finset.range (i + 1), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) = 1) := by sorry

end ConjGrad.ErrorDecrease.Supplement
