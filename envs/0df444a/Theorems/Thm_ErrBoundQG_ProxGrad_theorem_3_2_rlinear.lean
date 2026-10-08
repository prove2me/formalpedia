-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_2_rlinear
-- name    : ErrBoundQG.ProxGrad.theorem_3_2_rlinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:13.760577+00:00
-- url     : https://prove2.me/theorems/d4ac5fe9-551d-4969-a6f6-fdf83a707907
-- title:
--   Theorem 3.2, second claim, p. 5 (at t = 1/β) — under the error bound, the proximal gradient iterates converge R-linearly to a limit point
-- statement:
--   Let $g$, $f$, $\beta>0$, $\varphi=f+g$, $S\neq\emptyset$ and $\varphi^*$ be as in (3.1), and suppose the error bound condition holds with parameters $(\gamma,\nu)$, $\gamma,\nu>0$, for the step size $t=\beta^{-1}$. Let $(x_k)_{k\ge0}$ be iterates of the proximal gradient method,
--   $$x_{k+1} = \operatorname{prox}_{tg}\big(x_k - t\nabla f(x_k)\big),\qquad t=\beta^{-1},$$
--   and suppose $x^*$ is a limit point of $(x_k)$. Then there is an index $r$ such that $\varphi(x_r)$ is finite and, for all $k\ge1$,
--   $$\|x_{r+k}-x^*\|^2\ \le\ \Big(1-\frac{1}{2\beta\gamma}\Big)^k\, C\,\big(\varphi(x_r)-\varphi^*\big),\qquad C := \frac{2}{\beta\big(1-\sqrt{1-(2\beta\gamma)^{-1}}\big)^2}.$$
--
--   This is the R-linear convergence of the iterates that the error bound condition delivers.
--
--   **Formalization Note** The page states Theorem 3.2 for $t\le\beta^{-1}$, but its proof uses the descent inequality (3.2), $\varphi(x_k)-\varphi(x_{k+1})\ge\frac1{2\beta}\|\mathcal G_t(x_k)\|^2$, which holds at $t=\beta^{-1}$ and fails for $t<\beta^{-1}$ (for $f(x)=x^2/2$, $g=0$, $\beta=1$ the decrease is $(2t-t^2)x^2/2$). The statement is therefore made at $t=\beta^{-1}$ with $\beta>0$. The first claim of Theorem 3.2 (an iteration count) is not stated. "Limit point" is a cluster point of the sequence (`MapClusterPt`). The finiteness of $\varphi(x_r)$ is part of the conclusion so that $\varphi(x_r)-\varphi^*$ is a real number; $\sqrt{\cdot}$ is the real square root (equal to $0$ on negative arguments).
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 5, Theorem 3.2 (second claim), (3.2)–(3.4), Definition 3.1

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem theorem_3_2_rlinear {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : RockafellarMaxMono.Shared.ProperConvex g) (hgc : LowerSemicontinuous g)
    (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (β : ℝ) (hβ : 0 < β) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet (compositeObj f g))
    (hSne : S.Nonempty) (φstar : ℝ) (hstar : ∀ x ∈ S, compositeObj f g x = (φstar : EReal))
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (hEB : ErrorBound f g β⁻¹ S φstar γ ν)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, IsProxGradStep f g β⁻¹ (x k) (x (k + 1)))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : MapClusterPt xstar Filter.atTop x) :
    ∃ r : ℕ, ∃ c : ℝ, compositeObj f g (x r) = (c : EReal) ∧
      ∀ k : ℕ, 1 ≤ k →
        ‖x (r + k) - xstar‖ ^ 2 ≤
          (1 - 1 / (2 * β * γ)) ^ k *
            (2 / (β * (1 - Real.sqrt (1 - (2 * β * γ)⁻¹)) ^ 2)) * (c - φstar) := by sorry

end ErrBoundQG.ProxGrad
