-- Prove2me | Theorems.Thm_CubicRegNewton_LocalQuad_eq_2_5_first_order_condition
-- name    : CubicRegNewton.LocalQuad.eq_2_5_first_order_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:27:31.454321+00:00
-- url     : https://prove2.me/theorems/38bb1617-f2fd-4ba8-a924-c055d7541107
-- title:
--   (2.5): first-order condition satisfied by $T_M(x)$
-- statement:
--   Throughout, $F\subseteq\mathbb R^n$ is a closed convex set, $f$ is twice differentiable on $F$ with gradient $f'$ and Hessian $f''$, $x_0\in\operatorname{int}F$, the level set $\{x\in F: f(x)\le f(x_0)\}$ lies in $\operatorname{int}F$, and the Hessian is Lipschitz on $F$: $\|f''(x)-f''(y)\|\le L\|x-y\|$ for all $x,y\in F$, with $L>0$ (the standing assumptions of §2 and Assumption 1). Norms are Euclidean, and $\|A\|$ is the spectral norm. For $M>0$, $T_M(x)$ denotes any global minimizer over $y\in\mathbb R^n$ of the cubic model $\langle f'(x),y-x\rangle+\tfrac12\langle f''(x)(y-x),y-x\rangle+\tfrac M6\|y-x\|^3$ (2.4), and $r_M(x)=\|x-T_M(x)\|$.
--
--   Then for every $x\in F$ and $M>0$, every global minimizer $T=T_M(x)$ of the cubic model satisfies
--
--   $$
--   f'(x)+f''(x)(T-x)+\tfrac12M\|T-x\|\,(T-x)=0 .
--   $$
--
--   This is the stationarity equation of the cubic model; solving it for $T-x$ gives the step-length bound (3.9) and, with Lemma 1, the gradient bound of Lemma 3.
--
--   Differences from the source:
--   - encoding: f twice differentiable on the closed convex set F with non-empty interior (§2, p. 180) → the gradient f' and the Hessian f'' are given as data, with HasGradientWithinAt f (f' x) F x and HasFDerivWithinAt f' (f'' x) F x at every x ∈ F (StandingAssumptions); reason: derivatives within a convex set with non-empty interior are unique, so f' and f'' are the paper's gradient and Hessian on F; values off F play no role in the paper
--   - generalization: F contains the level set L(f(x0)) = {x ∈ Rⁿ : f(x) ≤ f(x0)} in its interior (§2, p. 180) → {x | x ∈ F ∧ f x ≤ f x₀} ⊆ interior F; reason: f is defined only on F in the paper, so its level set consists of points of F; the Lean hypothesis constrains no value of the Lean function f outside F and is implied by the literal reading {x | f x ≤ f x₀} ⊆ interior F, so the Lean statement specializes to the paper's
--   - encoding: ‖A‖ = λ1(AAᵀ)^{1/2}, the spectral norm (Notation, p. 180) → operator norm of f'' x - f'' y on EuclideanSpace ℝ (Fin n); reason: the operator norm for the Euclidean norm is the spectral norm
--   - encoding: T_M(x) ∈ Arg min_y of the model (2.4), chosen from the set of global minima (p. 181) → any T with IsMinOn (cubicModel f' f'' M x) Set.univ T; reason: the paper's Arg min over y ∈ Rⁿ is exactly the set of global minimizers; the run picks one per step
--   - encoding: x a point at which f'(x), f''(x) are evaluated (implicit) → hypothesis x ∈ F, and M > 0 (the positive parameter of (2.4), p. 181); reason: f, f', f'' are defined only on F in the paper, and M is a positive parameter throughout §2
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, (2.5), p. 182 (PDF p. 6)

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_StandingAssumptions
import Definitions.Def_CubicRegNewton_LocalQuad_cubicModel

namespace CubicRegNewton.LocalQuad

/-- **(2.5): the first-order condition satisfied by T_M(x).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, p. 182 (displayed, unnumbered statement):
"Note that point T_M(x) satisfies the following system of nonlinear equations:
f'(x) + f''(x)(y − x) + ½M‖y − x‖ · (y − x) = 0. (2.5)"

For `x ∈ F`, `M > 0` and any global minimizer `T` of the cubic model (2.4) at `x`,
`f'(x) + f''(x)(T − x) + (M/2)‖T − x‖ (T − x) = 0`.

**Formalization Note.** The standing assumptions (§2, p. 180; Assumption 1, p. 181) are `StandingAssumptions` (Readings 3, 4). `x ∈ F` is implicit on the page (`f''(x)` exists only on
`F`); `M > 0` is the page's "M be a positive parameter" (p. 181). The symmetry of `f''(x)`, needed
to differentiate the quadratic term, follows from the standing assumptions and is not assumed.
`T_M(x)` is any global minimizer (Reading 7). -/
theorem eq_2_5_first_order_condition {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {L : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hS : StandingAssumptions F f f' f'' L x₀)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F) {M : ℝ} (hM : 0 < M)
    {T : EuclideanSpace ℝ (Fin n)} (hT : IsMinOn (cubicModel f' f'' M x) Set.univ T) :
    f' x + f'' x (T - x) + (M / 2 * ‖T - x‖) • (T - x) = 0 := by sorry

end CubicRegNewton.LocalQuad
