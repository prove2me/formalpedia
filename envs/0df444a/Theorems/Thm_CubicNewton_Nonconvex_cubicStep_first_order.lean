-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_cubicStep_first_order
-- name    : CubicNewton.Nonconvex.cubicStep_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:16:37.258986+00:00
-- url     : https://prove2.me/theorems/6bd1c634-43cc-494e-97c5-78f554fc3e80
-- title:
--   Eq. (2.5): the first-order condition satisfied by a cubic step $T_M(x)$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   For $M > 0$ let $T = T_M(x)$ be **any global minimizer** over $y \in \mathbb{R}^n$ of the cubic model
--   $$\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3,$$
--   and write $r_M(x) = \|x - T_M(x)\|$.
--
--   Then for every $x \in F$ the step $T = T_M(x)$ satisfies the system of nonlinear equations
--   $$f'(x) + f''(x)(T - x) + \tfrac12 M\,\|T - x\|\,(T - x) = 0 .$$
--   This is the stationarity condition of the cubic model at its global minimizer. Taking the inner product with $T - x$ gives relation (2.6), used in Lemmas 2 and 4; its norm form is used in Lemma 3.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Section 2, Eq. (2.5)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Section 2, Eq. (2.5), p. 182: every global minimizer `T = T_M(x)`
of the cubic model satisfies `f′(x) + f″(x)(T − x) + ½M‖T − x‖·(T − x) = 0`. -/
theorem cubicStep_first_order {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by sorry

end CubicNewton.Nonconvex
