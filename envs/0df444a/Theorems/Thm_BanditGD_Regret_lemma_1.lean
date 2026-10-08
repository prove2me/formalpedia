-- Prove2me | Theorems.Thm_BanditGD_Regret_lemma_1
-- name    : BanditGD.Regret.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:05:04.353987+00:00
-- url     : https://prove2.me/theorems/cb16ba7f-ec5a-4521-b96e-a2db5f3cd66e
-- title:
--   Lemma 1, p. 5 — E_{u∈𝕊}[f(x + δu)u] = (δ/d)∇f̂(x)
-- statement:
--   Let $d\ge1$, let $\mathbb B$ and $\mathbb S$ be the closed unit ball and the unit sphere of $\mathbb R^d$, and fix $\delta>0$. For $f:\mathbb R^d\to\mathbb R$ let
--   $$\hat f(z)=\mathbb E_{v\in\mathbb B}\big[f(z+\delta v)\big]$$
--   be its average over the ball of radius $\delta$ around $z$, with $v$ uniform on $\mathbb B$. Let $x\in\mathbb R^d$ and suppose $f$ is continuous on an open set containing the closed ball $x+\delta\mathbb B$. Then $\hat f$ is differentiable at $x$ and, with $u$ uniform on $\mathbb S$,
--   $$\nabla\hat f(x)=\frac d\delta\,\mathbb E_{u\in\mathbb S}\big[f(x+\delta u)\,u\big],\qquad\text{i.e.}\qquad \mathbb E_{u\in\mathbb S}\big[f(x+\delta u)\,u\big]=\frac\delta d\,\nabla\hat f(x).$$
--
--   The lemma says that a single evaluation of $f$ at a random point of the sphere $x+\delta\mathbb S$, multiplied by the direction, is an unbiased estimate (up to the factor $\delta/d$) of the gradient of the smoothed function $\hat f$. It is what makes gradient descent possible with one function value per round.
--
--   **Formalization Note** The paper states the lemma "for any function $f$" and remarks that $\hat f$ is differentiable even when $f$ is not. Without any regularity the identity fails: a function that is $0$ inside the ball and $1$ on the sphere $x+\delta\mathbb S$ has the same $\hat f$ near $x$ as the zero function but a nonzero sphere average. The hypothesis of continuity on an open neighbourhood of $x+\delta\mathbb B$ is added; it is exactly what the application in Theorem 1 supplies (there $x+\delta\mathbb B$ lies in the interior of the feasible set, where convex costs are continuous). The conclusion is stated with `HasGradientAt`, so differentiability of $\hat f$ at $x$ is part of the claim. $\hat f$ is the published `smoothedLoss d δ f` and the uniform law on the sphere is the published `uniformSphere d`.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 5, Lemma 1 (with the definition (4) of f̂)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
open MeasureTheory

namespace BanditGD.Regret

theorem lemma_1 {d : ℕ} (hd : 1 ≤ d) (f : EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (hxU : Metric.closedBall x δ ⊆ U) (hf : ContinuousOn f U) :
    HasGradientAt (RegretBandits.Nonlinear.smoothedLoss d δ f)
      (((d : ℝ) / δ) • ∫ v, f (x + δ • v) • v ∂(RegretBandits.Nonlinear.uniformSphere d)) x := by sorry

end BanditGD.Regret
