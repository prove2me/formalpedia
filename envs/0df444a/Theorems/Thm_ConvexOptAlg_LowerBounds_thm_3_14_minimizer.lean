-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_thm_3_14_minimizer
-- name    : ConvexOptAlg.LowerBounds.thm_3_14_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:44:25.137613+00:00
-- url     : https://prove2.me/theorems/b25182d8-cfca-4635-9485-fb79bd59e982
-- title:
--   Proof of Theorem 3.14, p. 282 — x*_k(i) = 1 − i/(k+1) solves A_k x = e₁, minimizes f_k, and f*_k = −(β/8)(1 − 1/(k+1))
-- statement:
--   Let $\beta>0$ and $1\le k\le n$. Let $f_k(x)=\frac\beta8x^\top A_kx-\frac\beta4x^\top e_1$ on $\mathbb R^n$ and $f_k^*=\inf_{x\in\mathbb R^n}f_k(x)$. Let $x^*_k$ be the point with $x^*_k(i)=1-\frac{i}{k+1}$ for $i=1,\dots,k$ and $x^*_k(i)=0$ for $i>k$. Then:
--
--   1. $A_kx^*_k=e_1$, $x^*_k\in\mathrm{Span}(e_1,\dots,e_k)$, and $x^*_k$ is the only solution of $A_kx=e_1$ in that span;
--   2. $x^*_k$ minimizes $f_k$ over $\mathbb R^n$, so $f_k^*=f_k(x^*_k)$;
--   3. the minimal value is
--   $$f_k^*=\frac\beta8(x^*_k)^\top A_kx^*_k-\frac\beta4(x^*_k)^\top e_1=-\frac\beta8(x^*_k)^\top e_1=-\frac\beta8\Bigl(1-\frac1{k+1}\Bigr).$$
--
--   These values feed the closing computation of Theorem 3.14.
--
--   **Formalization Note** The infimum is the real `⨅`; it is a genuine infimum here because the statement also asserts that $x^*_k$ attains it.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282. For `1 ≤ k ≤ n` and `β > 0`, the point
`x*_k` with `x*_k(i) = 1 − i/(k+1)` (`i = 1, …, k`, zero beyond) is the unique solution in
`Span(e₁, …, e_k)` of `A_k x = e₁`; it minimizes `f_k(x) = (β/8)xᵀA_k x − (β/4)xᵀe₁` over `ℝⁿ`, and
`f*_k = inf_{x∈ℝⁿ} f_k(x) = f_k(x*_k) = −(β/8)(x*_k)ᵀe₁ = −(β/8)(1 − 1/(k+1))`. -/
theorem thm_3_14_minimizer (n k : ℕ) (β : ℝ) (hβ : 0 < β) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (tridiag n k).mulVec (xstarK n k).ofLp = (basisVec n 1).ofLp ∧
      xstarK n k ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k) ∧
      (∀ y ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k),
        (tridiag n k).mulVec y.ofLp = (basisVec n 1).ofLp → y = xstarK n k) ∧
      (∀ y, fK n β k (xstarK n k) ≤ fK n β k y) ∧
      ⨅ y, fK n β k y = fK n β k (xstarK n k) ∧
      fK n β k (xstarK n k) = -(β / 8) * ⟪xstarK n k, basisVec n 1⟫_ℝ ∧
      fK n β k (xstarK n k) = -(β / 8) * (1 - 1 / ((k : ℝ) + 1)) := by sorry

end ConvexOptAlg.LowerBounds
