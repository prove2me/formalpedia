-- Prove2me | Theorems.Thm_ErrBoundQG_General_theorem_8_11
-- name    : ErrBoundQG.General.theorem_8_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:42.10799+00:00
-- url     : https://prove2.me/theorems/f39b7285-17ff-4faf-96c3-807e0a24f33b
-- title:
--   Theorem 8.11, p. 31 — subregularity of ∂φ and of the prox-gradient map 𝒢_t coincide (attentively; outright for convex h)
-- statement:
--   Consider the composite problem (8.2), $\min_x\varphi(x)=h(c(x))$, with $c:\mathbb R^n\to\mathbb R^m$ $C^1$-smooth and $h:\mathbb R^m\to\overline{\mathbb R}$ closed, and a point $\bar x$ with $c\pitchfork_{\bar x}h$ and $0\in\partial\varphi(\bar x)$. Suppose $\nabla c$ is Lipschitz around $\bar x$ and $h$ is prox-regular at $c(\bar x)$ for every subgradient $w\in\partial h(c(\bar x))$ with $0=\nabla c(\bar x)^*w$. For $t>0$ let $\mathcal G_t(x)=t^{-1}(x-\mathcal S_t(x))$ be the prox-gradient mapping, $\mathcal S_t(x)$ the stationary points of $\varphi_t(x;\cdot)$. Consider
--
--   - (i) there is a $\varphi$-attentive localization of $\partial\varphi$ that is metrically subregular at $(\bar x,0)$;
--   - (ii) there is a $\varphi(\cdot,\cdot)$-attentive localization of $\mathcal G_t$ that is metrically subregular at $(\bar x,0)$.
--
--   Then:
--
--   1. (i) $\Rightarrow$ (ii) holds for every $t>0$;
--   2. there is $\bar t>0$ such that (ii) $\Rightarrow$ (i) for every $t\in(0,\bar t)$;
--   3. when $h$ is convex, for every $t>0$,
--   $$\partial\varphi\text{ is metrically subregular at }(\bar x,0)\iff\mathcal G_t\text{ is metrically subregular at }(\bar x,0).$$
--
--   Subregularity of $\mathcal G_t$ at $(\bar x,0)$ is the error bound property of the prox-linear method; the theorem extends the equivalence of Theorem 5.10 from finite convex $h$ to closed, prox-regular $h$.
--
--   **Formalization Note** The page writes "$\bar t\ge0$"; with $\bar t=0$ part 2 would be vacuous, and its proof obtains a positive $\bar t$, so $\bar t>0$ is required. Subregularity at $(\bar x,0)$ includes $0\in F(\bar x)$ and a constant $l>0$. "$h$ convex" is the convexity inequality $h((1-s)y+sz)\le(1-s)h(y)+sh(z)$, $0<s<1$, in $\overline{\mathbb R}$; the theorem's other hypotheses stay in force in part 3. $h$ is `EReal`-valued, lower semicontinuous and never $-\infty$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 31, Theorem 8.11

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem theorem_8_11 {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (hc : ContDiff ℝ 1 c)
    (h : ErrBoundQG.ProxLin.En m → EReal) (hlsc : LowerSemicontinuous h) (hbot : ∀ y, h y ≠ ⊥)
    (xbar : ErrBoundQG.ProxLin.En n) (htr : Transverse c h xbar) (hstat : 0 ∈ limSubdiff (phi h c) xbar)
    (hlip : JacLipAround c xbar)
    (hpr : ∀ w ∈ limSubdiff h (c xbar),
      ContinuousLinearMap.adjoint (fderiv ℝ c xbar) w = 0 → ProxRegularAt h (c xbar) w) :
    (∀ t : ℝ, 0 < t →
      (∃ (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) (l : ℝ),
          IsAttentiveLocSubdiff h c xbar W ∧ IsMetricSubregularAt W xbar 0 l) →
        ∃ (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) (l : ℝ),
          IsAttentiveLocGrad h c t xbar W ∧ IsMetricSubregularAt W xbar 0 l) ∧
    (∃ tbar : ℝ, 0 < tbar ∧ ∀ t ∈ Set.Ioo (0 : ℝ) tbar,
      (∃ (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) (l : ℝ),
          IsAttentiveLocGrad h c t xbar W ∧ IsMetricSubregularAt W xbar 0 l) →
        ∃ (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) (l : ℝ),
          IsAttentiveLocSubdiff h c xbar W ∧ IsMetricSubregularAt W xbar 0 l) ∧
    (IsConvexE h → ∀ t : ℝ, 0 < t →
      ((∃ l : ℝ, IsMetricSubregularAt (limSubdiff (phi h c)) xbar 0 l) ↔
        (∃ l : ℝ, IsMetricSubregularAt (gradMap h c t) xbar 0 l))) := by sorry

end ErrBoundQG.General
