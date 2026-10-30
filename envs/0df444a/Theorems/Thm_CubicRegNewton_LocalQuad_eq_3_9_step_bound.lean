-- Prove2me | Theorems.Thm_CubicRegNewton_LocalQuad_eq_3_9_step_bound
-- name    : CubicRegNewton.LocalQuad.eq_3_9_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:36.13037+00:00
-- url     : https://prove2.me/theorems/036ce4f9-bdae-4355-838a-34f0374e4cef
-- title:
--   (3.9): the cubic step is at most $\|f'(x)\|/\lambda_n(f''(x))$
-- statement:
--   Throughout, $F\subseteq\mathbb R^n$ is a closed convex set, $f$ is twice differentiable on $F$ with gradient $f'$ and Hessian $f''$, $x_0\in\operatorname{int}F$, the level set $\{x\in F: f(x)\le f(x_0)\}$ lies in $\operatorname{int}F$, and the Hessian is Lipschitz on $F$: $\|f''(x)-f''(y)\|\le L\|x-y\|$ for all $x,y\in F$, with $L>0$ (the standing assumptions of §2 and Assumption 1). Norms are Euclidean, and $\|A\|$ is the spectral norm. For $M>0$, $T_M(x)$ denotes any global minimizer over $y\in\mathbb R^n$ of the cubic model $\langle f'(x),y-x\rangle+\tfrac12\langle f''(x)(y-x),y-x\rangle+\tfrac M6\|y-x\|^3$ (2.4), and $r_M(x)=\|x-T_M(x)\|$. Let $\lambda_n(H)$ denote the least eigenvalue of a symmetric matrix $H$.
--
--   Let $x\in F$ with $f''(x)\succ0$ and let $M>0$. Then
--
--   $$
--   r_M(x)=\|T_M(x)-x\|=\big\|\big(f''(x)+r_M(x)\tfrac M2 I\big)^{-1}f'(x)\big\|\le\frac{\|f'(x)\|}{\lambda_n(f''(x))} .
--   $$
--
--   At $x=x_k$, $M=M_k$ this is (3.9) of the proof of Theorem 3: the regularized step is never longer than the pure Newton step bound.
--
--   Differences from the source:
--   - encoding: f twice differentiable on the closed convex set F with non-empty interior (§2, p. 180) → the gradient f' and the Hessian f'' are given as data, with HasGradientWithinAt f (f' x) F x and HasFDerivWithinAt f' (f'' x) F x at every x ∈ F (StandingAssumptions); reason: derivatives within a convex set with non-empty interior are unique, so f' and f'' are the paper's gradient and Hessian on F; values off F play no role in the paper
--   - generalization: F contains the level set L(f(x0)) = {x ∈ Rⁿ : f(x) ≤ f(x0)} in its interior (§2, p. 180) → {x | x ∈ F ∧ f x ≤ f x₀} ⊆ interior F; reason: f is defined only on F in the paper, so its level set consists of points of F; the Lean hypothesis constrains no value of the Lean function f outside F and is implied by the literal reading {x | f x ≤ f x₀} ⊆ interior F, so the Lean statement specializes to the paper's
--   - encoding: ‖A‖ = λ1(AAᵀ)^{1/2}, the spectral norm (Notation, p. 180) → operator norm of f'' x - f'' y on EuclideanSpace ℝ (Fin n); reason: the operator norm for the Euclidean norm is the spectral norm
--   - encoding: λn(H), the least eigenvalue of a symmetric matrix (Notation, p. 180) → lamMin H = ⨅ over unit vectors u of ⟪H u, u⟫ (Rayleigh infimum; 0 when n = 0); reason: for symmetric H and n ≥ 1 the Rayleigh infimum is the least eigenvalue; the Hessians on F are symmetric under the standing assumptions; for n = 0 every statement holds trivially
--   - encoding: H ≻ 0 (positive definite) → ∀ u ≠ 0, 0 < ⟪H u, u⟫; reason: the definition of positive definiteness for a symmetric matrix
--   - encoding: T_M(x) ∈ Arg min_y of the model (2.4), chosen from the set of global minima (p. 181) → any T with IsMinOn (cubicModel f' f'' M x) Set.univ T; reason: the paper's Arg min over y ∈ Rⁿ is exactly the set of global minimizers; the run picks one per step
--   - encoding: x a point at which f'(x), f''(x) are evaluated (implicit) → hypothesis x ∈ F, and M > 0 (the positive parameter of (2.4), p. 181); reason: f, f', f'' are defined only on F in the paper, and M is a positive parameter throughout §2
--   - generalization: stated for an iterate xk of (3.5) with f''(xk) ≻ 0 and δk ≤ 1/4, M = Mk → any x ∈ F with f''(x) ≻ 0 and any M > 0; reason: the bound uses only (2.5) and positive definiteness at x; the iterates of (3.5) are special cases
--   - encoding: (f''(xk) + rMk(xk)(Mk/2)I)^{−1} → Ring.inverse (f'' x + (‖T − x‖ * (M / 2)) • ContinuousLinearMap.id ℝ _); reason: the operator is positive definite plus a nonnegative multiple of I, hence invertible, so Ring.inverse is its true inverse and never the junk value 0
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, proof of Theorem 3, (3.9), p. 187 (PDF p. 11)

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_StandingAssumptions
import Definitions.Def_CubicRegNewton_LocalQuad_cubicModel
import Definitions.Def_CubicRegNewton_LocalQuad_lamMin

open scoped InnerProductSpace

namespace CubicRegNewton.LocalQuad

/-- **(3.9): the cubic step is no longer than ‖f'(x)‖/λₙ(f''(x)).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, proof of Theorem 3, (3.9), p. 187:
"Assume that for some k ≥ 0 we have f''(xk) ≻ 0. [...] From equation (2.5) we have
r_Mk(xk) = ‖T_Mk(xk) − xk‖ = ‖(f''(xk) + r_Mk(xk)(Mk/2)I)⁻¹ f'(xk)‖ ≤ ‖f'(xk)‖/λn(f''(xk)). (3.9)"

For `x ∈ F` with `f''(x) ≻ 0`, any `M > 0` and any global minimizer `T` of the cubic model at
`x`, `‖T − x‖ = ‖(f''(x) + ‖T − x‖(M/2)I)⁻¹ f'(x)‖ ≤ ‖f'(x)‖ / λₙ(f''(x))`.

**Formalization Note.** The standing assumptions (§2, p. 180; Assumption 1, p. 181) are `StandingAssumptions` (Readings 3, 4). The statement is made at one point `x ∈ F` with any `M > 0`
(at `x = x_k`, `M = M_k` it is (3.9)). Both the middle equality and the inequality of the
display are stated. The inverse is `Ring.inverse` in the ring `E →L[ℝ] E`; the operator
`f''(x) + ‖T − x‖(M/2)I` is invertible (positive definite plus a nonnegative multiple of `I`), so
this is the true inverse, not the junk value `0`.
`f''(x) ≻ 0` is `∀ u ≠ 0, 0 < ⟪f''(x) u, u⟫` (Reading 6); `λₙ` is `lamMin` (Reading 5). -/
theorem eq_3_9_step_bound {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {L : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hS : StandingAssumptions F f f' f'' L x₀)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F)
    (hpdx : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪f'' x u, u⟫_ℝ)
    {M : ℝ} (hM : 0 < M)
    {T : EuclideanSpace ℝ (Fin n)} (hT : IsMinOn (cubicModel f' f'' M x) Set.univ T) :
    ‖T - x‖ =
        ‖Ring.inverse (f'' x + (‖T - x‖ * (M / 2)) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (f' x)‖ ∧
      ‖Ring.inverse (f'' x + (‖T - x‖ * (M / 2)) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (f' x)‖ ≤
        ‖f' x‖ / lamMin (f'' x) := by sorry

end CubicRegNewton.LocalQuad
