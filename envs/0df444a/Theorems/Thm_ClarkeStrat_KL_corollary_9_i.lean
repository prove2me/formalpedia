-- Prove2me | Theorems.Thm_ClarkeStrat_KL_corollary_9_i
-- name    : ClarkeStrat.KL.corollary_9_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:31.813264+00:00
-- url     : https://prove2.me/theorems/d89a97b5-572c-47ba-8101-ef4c35c44e0e
-- title:
--   Corollary 9 (15) and (i), p. 564 — Proj_{T_x X_x} ∂°f(x) ⊂ {∇_R f(x)} and ‖∇_R f(x)‖ ≤ ‖x*‖ for definable f
-- statement:
--   Let $\mathcal O$ be an o-minimal structure, $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ a lower semicontinuous function definable in $\mathcal O$, and $p\ge1$ an integer. Then there is a finite definable $C^p$-Whitney stratification $\mathcal X=(X_i)_{i\in I}$ of $\operatorname{dom} f$ such that the restriction of $f$ to each stratum has a Riemannian gradient $\nabla_R f(x)$ at every point $x$ of the stratum, and for every $x\in X_i$ and every Clarke subgradient $x^*\in\partial^\circ f(x)$,
--   $$\operatorname{Proj}_{T_xX_i}x^*=\nabla_R f(x)\qquad\text{and}\qquad\|\nabla_R f(x)\|\le\|x^*\|.$$
--   In the paper's notation, $\operatorname{Proj}_{T_xX_x}\partial^\circ f(x)\subset\{\nabla_R f(x)\}$ (15), and consequence (i).
--
--   This "definable projection formula" is what lets the smooth Kurdyka–Łojasiewicz inequality on each stratum control every Clarke subgradient, which is how Theorem 14 is reached.
--
--   **Formalization Note** The existence of $\nabla_R f(x)$ on each stratum is stated explicitly; the paper presupposes it (the restrictions of $f$ to the strata are $C^1$), and stating it prevents the projection clause from holding vacuously. The Riemannian gradient is relative to the stratum $X_i$ containing $x$; $X_i\subseteq\operatorname{dom} f$, so the real value of $f$ is used on it. $f$ is assumed never equal to $-\infty$.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), p. 564, Corollary 9, (15) and (i)

import Mathlib
import Definitions.Def_ClarkeStrat_KL_Setting

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

/-- Corollary 9, (15) and (i), p. 564 (Morse–Sard theorem for definable functions): for a definable
lower semicontinuous `f : ℝⁿ → ℝ ∪ {+∞}` and `p ≥ 1` there is a finite definable `C^p`-Whitney
stratification `(X_i)` of `dom f` on whose strata the Riemannian gradient `∇_R f` exists, such that
every Clarke subgradient `x*` at `x ∈ X_i` projects orthogonally onto `T_x X_i` as `∇_R f(x)`, and
`‖∇_R f(x)‖ ≤ ‖x*‖`. -/
theorem corollary_9_i (O : OMinimalStructure) {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hdef : graphSet f ∈ O.O (n + 1)) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (ℓ : ℕ) (X : Fin ℓ → Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, X i ∈ O.O n) ∧ IsCpStratification p {x | f x ≠ ⊤} X ∧ WhitneyA X ∧
      (∀ i, ∀ x ∈ X i, ∃ g, IsRiemGrad (fun y => (f y).toReal) (X i) x g) ∧
      ∀ i, ∀ x ∈ X i, ∀ g, IsRiemGrad (fun y => (f y).toReal) (X i) x g →
        ∀ v ∈ ClarkeSubdiff f x, (tangentSpace (X i) x).starProjection v = g ∧ ‖g‖ ≤ ‖v‖ := by sorry

end ClarkeStrat.KL
