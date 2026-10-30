-- Prove2me | Theorems.Thm_CubicRegNewton_LocalQuad_lemma_1
-- name    : CubicRegNewton.LocalQuad.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:26:58.629671+00:00
-- url     : https://prove2.me/theorems/10759941-452e-47ca-977b-843401627c02
-- title:
--   Lemma 1: Taylor bounds (2.2)–(2.3) from the Lipschitz Hessian
-- statement:
--   Throughout, $F\subseteq\mathbb R^n$ is a closed convex set, $f$ is twice differentiable on $F$ with gradient $f'$ and Hessian $f''$, $x_0\in\operatorname{int}F$, the level set $\{x\in F: f(x)\le f(x_0)\}$ lies in $\operatorname{int}F$, and the Hessian is Lipschitz on $F$: $\|f''(x)-f''(y)\|\le L\|x-y\|$ for all $x,y\in F$, with $L>0$ (the standing assumptions of §2 and Assumption 1). Norms are Euclidean, and $\|A\|$ is the spectral norm.
--
--   Then for all $x,y\in F$,
--
--   $$
--   \|f'(y)-f'(x)-f''(x)(y-x)\|\le\tfrac12L\|y-x\|^2,
--   $$
--
--   $$
--   \Bigl|f(y)-f(x)-\langle f'(x),y-x\rangle-\tfrac12\langle f''(x)(y-x),y-x\rangle\Bigr|\le\frac L6\|y-x\|^3.
--   $$
--
--   These are the first- and second-order Taylor bounds that a Lipschitz Hessian provides; every estimate in the analysis of the cubic Newton step rests on them.
--
--   Differences from the source:
--   - encoding: f twice differentiable on the closed convex set F with non-empty interior (§2, p. 180) → the gradient f' and the Hessian f'' are given as data, with HasGradientWithinAt f (f' x) F x and HasFDerivWithinAt f' (f'' x) F x at every x ∈ F (StandingAssumptions); reason: derivatives within a convex set with non-empty interior are unique, so f' and f'' are the paper's gradient and Hessian on F; values off F play no role in the paper
--   - generalization: F contains the level set L(f(x0)) = {x ∈ Rⁿ : f(x) ≤ f(x0)} in its interior (§2, p. 180) → {x | x ∈ F ∧ f x ≤ f x₀} ⊆ interior F; reason: f is defined only on F in the paper, so its level set consists of points of F; the Lean hypothesis constrains no value of the Lean function f outside F and is implied by the literal reading {x | f x ≤ f x₀} ⊆ interior F, so the Lean statement specializes to the paper's
--   - encoding: ‖A‖ = λ1(AAᵀ)^{1/2}, the spectral norm (Notation, p. 180) → operator norm of f'' x - f'' y on EuclideanSpace ℝ (Fin n); reason: the operator norm for the Euclidean norm is the spectral norm
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, doi:10.1007/s10107-006-0706-8, Lemma 1, (2.2)–(2.3), p. 181 (PDF p. 5)

import Mathlib
import Definitions.Def_CubicRegNewton_LocalQuad_StandingAssumptions

open scoped InnerProductSpace

namespace CubicRegNewton.LocalQuad

/-- **Lemma 1, (2.2)–(2.3).**
Nesterov & Polyak, *Cubic regularization of Newton method and its global performance*,
Math. Program. Ser. A 108 (2006) 177–205, Lemma 1, p. 181:
"For any x and y from F we have
‖f'(y) − f'(x) − f''(x)(y − x)‖ ≤ ½L‖y − x‖², (2.2)
|f(y) − f(x) − ⟨f'(x), y − x⟩ − ½⟨f''(x)(y − x), y − x⟩| ≤ (L/6)‖y − x‖³. (2.3)"

**Formalization Note.** The standing assumptions (§2, p. 180; Assumption 1, p. 181) are `StandingAssumptions` (Readings 3, 4). Both bounds form one item, as in the lemma. -/
theorem lemma_1 {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {L : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hS : StandingAssumptions F f f' f'' L x₀) :
    ∀ x ∈ F, ∀ y ∈ F,
      ‖f' y - f' x - f'' x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 ∧
      |f y - f x - ⟪f' x, y - x⟫_ℝ - 1 / 2 * ⟪f'' x (y - x), y - x⟫_ℝ| ≤ L / 6 * ‖y - x‖ ^ 3 := by sorry

end CubicRegNewton.LocalQuad
