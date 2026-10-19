-- Prove2me | Theorems.Thm_CauchyRiemannIndex_linearIndependent_cokernel_of_adjoint_small
-- name    : CauchyRiemannIndex.linearIndependent_cokernel_of_adjoint_small
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:09:26.378513+00:00
-- url     : https://prove2.me/theorems/6fb21bb3-9c4c-48b9-8d1f-1398f9e8af44
-- title:
--   Independent cokernel elements of a Cauchy–Riemann operator from approximate solutions of the adjoint equation
-- statement:
--   Let $T:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous and bounded, and let $D_T\eta=\partial_s\eta+J_0\partial_t\eta+T\eta$, acting from $W^{1,2}(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ to $L^2$, with formal adjoint $D_T^*v=-\partial_sv+J_0\partial_tv+T^{\mathsf T}v$. Suppose that for some $c\ge0$
--   $$\|\eta\|_{L^2}^2\le c\,\|D_T\eta\|_{L^2}^2\qquad\text{for all }\eta\in W^{1,2},$$
--   and let $v_1,\dots,v_k$ be smooth sections, $1$-periodic in $t$ and vanishing for large $|s|$, such that every nonzero combination $v=\sum_i g_iv_i$ ($g\in\mathbb{R}^k\setminus\{0\}$) satisfies
--   $$c\,\|D_T^*v\|_{L^2}^2<\|v\|_{L^2}^2 .$$
--   Then the cokernel $L^2/\operatorname{im}D_T$ contains $k$ linearly independent elements; in particular $\dim\operatorname{coker}D_T\ge k$.
--
--   **Formalization Note** $W^{1,2}$ is `W1p 2 n`, $\|D_T\eta\|_{L^2}$ is the $L^2$ norm of `crApply T` on a triple, and the norms in the estimate are written with `eLpNorm` (values in $[0,\infty]$, with $c$ entering through `ENNReal.ofReal`). The test sections are `IsTestSection`, and $D_T^*v$ is written out with `partialS`, `partialT` and the transpose `(T x)ᵀ`. Boundedness of $T$ is the bound $|T(x)v|\le M|v|$ for all $x$ and $v$. The image is the submodule `crRange 2 T` of `LpCyl n 2`, and the conclusion is a linearly independent family `Fin k → LpCyl n 2 ⧸ crRange 2 T`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lectures 4–5 (operators D_S = ∂_s + J_0 ∂_t + S on the cylinder, formal adjoint, cokernel); used for Proposition 5.24 (formal adjoint) and Proposition 5.27, p = 2

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Lower bound for the cokernel of `D_T = ∂ₛ + J₀ ∂ₜ + T : W^{1,2} → L²` on the cylinder, for a
continuous bounded coefficient `T`: suppose `‖η‖²_{L²} ≤ c ‖D_T η‖²_{L²}` on
`W^{1,2}`, and let `v₁, …, v_k` be test sections such that every nonzero combination `v = Σ gᵢ vᵢ`
satisfies `c ‖D_T* v‖²_{L²} < ‖v‖²_{L²}`, where `D_T* v = -∂ₛ v + J₀ ∂ₜ v + Tᵀ v` is the formal
adjoint. Then the cokernel `L² / im D_T` contains `k` linearly independent elements. -/
theorem linearIndependent_cokernel_of_adjoint_small (n : ℕ) (T : ℝ × ℝ → Mat n)
    (hT : Continuous T)
    (hTb : ∃ M : ℝ, ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (T x) v‖ ≤ M * ‖v‖)
    (c : ℝ) (hc : 0 ≤ c)
    (hest : ∀ w ∈ W1p 2 n, eLpNorm (w.1 : ℝ × ℝ → Vec n) 2 cylMeasure ^ 2 ≤
      ENNReal.ofReal c * eLpNorm (crApply T w) 2 cylMeasure ^ 2)
    (k : ℕ) (v : Fin k → ℝ × ℝ → Vec n) (hv : ∀ i, IsTestSection (v i))
    (hsmall : ∀ g : Fin k → ℝ, g ≠ 0 →
      c * ∫ x, ‖∑ i, g i • (-partialS (v i) x + Matrix.toEuclideanLin (J₀ n) (partialT (v i) x) +
        Matrix.toEuclideanLin (T x)ᵀ (v i x))‖ ^ 2 ∂cylMeasure <
      ∫ x, ‖∑ i, g i • v i x‖ ^ 2 ∂cylMeasure) :
    ∃ u : Fin k → LpCyl n 2 ⧸ crRange 2 T, LinearIndependent ℝ u := by
  sorry

end CauchyRiemannIndex
