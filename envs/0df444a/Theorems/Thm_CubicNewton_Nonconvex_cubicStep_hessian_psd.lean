-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_cubicStep_hessian_psd
-- name    : CubicNewton.Nonconvex.cubicStep_hessian_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:17:15.611051+00:00
-- url     : https://prove2.me/theorems/844698b3-14af-42b2-b9b1-0413d8507bd2
-- title:
--   Proposition 1 (2.7): $f''(x) + \frac12 M r_M(x) I \succeq 0$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   For $M > 0$ let $T = T_M(x)$ be **any global minimizer** over $y \in \mathbb{R}^n$ of the cubic model
--   $$\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3,$$
--   and write $r_M(x) = \|x - T_M(x)\|$.
--
--   Then for any $x \in F$,
--   $$f''(x) + \tfrac12 M\, r_M(x)\, I \succeq 0,$$
--   that is, $\langle f''(x) v, v\rangle + \tfrac12 M\, r_M(x)\,\|v\|^2 \ge 0$ for every $v \in \mathbb{R}^n$.
--   This is the second-order property of a **global** minimizer of the cubic model; it fails for a merely stationary point. It drives the sign relation (2.8), the model decrease (2.11), and the eigenvalue part of Lemma 5.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point. The matrix inequality is written as nonnegativity of the quadratic form.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Proposition 1, (2.7)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Proposition 1, (2.7), p. 182: `f″(x) + ½ M r_M(x) I ⪰ 0`, written as
nonnegativity of the quadratic form, where `r_M(x) = ‖x − T‖` for any global minimizer `T`. -/
theorem cubicStep_hessian_psd {n : ℕ}
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
    ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H x v, v⟫ + 1 / 2 * M * ‖x - T‖ * ‖v‖ ^ 2 := by sorry

end CubicNewton.Nonconvex
