-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_6
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:59:22.274522+00:00
-- url     : https://prove2.me/theorems/d0cbb3c7-47e8-4ff5-8f23-e81330604a60
-- title:
--   Theorem 6:6 — projections on the line $x_0h$ advance monotonically to $h$
-- statement:
--   Let $x_0,\dots,x_m=h$ be the cg estimates for a real symmetric positive definite $A$. The projection of $x_j$ on the line through $x_0$ and $h$ is $x_j'=x_0+s_j(h-x_0)$, with
--
--   $$s_j=\frac{(x_j-x_0,\,h-x_0)}{|h-x_0|^2} .$$
--
--   The points $x_0,x_1',\dots,x_{m-1}',x_m=h$ lie in the order of enumeration: $s_0=0<s_1<\cdots<s_{m-1}<s_m=1$.
--
--   The cg-method thus proceeds towards the solution without oscillation along the line from the initial point to the solution.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - encoding: $m\ge1$ implicit (the line $x_0h$ exists) → the conclusion $s_m=1$ is asserted for $0<m$; for $m=0$ the remaining clauses are trivial; reason: the case $m=0$ ($x_0=h$) has no line and no intermediate points
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 417, Theorem 6:6 (PDF p. 9)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:6 (Hestenes–Stiefel 1952, p. 417): the projection of `xⱼ` on the line through `x₀`
and `xₘ = h` is `x₀ + sⱼ(h − x₀)` with `sⱼ = (xⱼ − x₀, h − x₀)/|h − x₀|²`, and
`0 = s₀ < s₁ < ⋯ < s_{m−1} < sₘ = 1`; `m` is the step at which the cg-method terminates. -/
theorem theorem_6_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ j : ℕ, ((cgIter A k x₀ j).x - (x₀ + (((cgIter A k x₀ j).x - x₀) ⬝ᵥ (h - x₀) /
        ((h - x₀) ⬝ᵥ (h - x₀))) • (h - x₀))) ⬝ᵥ (h - x₀) = 0) ∧
    ((cgIter A k x₀ 0).x - x₀) ⬝ᵥ (h - x₀) / ((h - x₀) ⬝ᵥ (h - x₀)) = 0 ∧
    (0 < m → ((cgIter A k x₀ m).x - x₀) ⬝ᵥ (h - x₀) / ((h - x₀) ⬝ᵥ (h - x₀)) = 1) ∧
    (∀ j : ℕ, j < m →
      ((cgIter A k x₀ j).x - x₀) ⬝ᵥ (h - x₀) / ((h - x₀) ⬝ᵥ (h - x₀)) <
        ((cgIter A k x₀ (j + 1)).x - x₀) ⬝ᵥ (h - x₀) / ((h - x₀) ⬝ᵥ (h - x₀))) := by sorry

end ConjGrad.ErrorDecrease.Supplement
