-- Prove2me | Theorems.Thm_ActiveSaddleSGD_theorem_3
-- name    : ActiveSaddleSGD.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:40.673877+00:00
-- url     : https://prove2.me/theorems/78df022a-87c2-4828-893e-94dcfeffff94
-- title:
--   Theorem 3 — stochastic subgradient descent almost surely does not converge to an active strict saddle
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be path differentiable and let
--   $$
--   x_{n+1}=x_n-\gamma_nv_n+\gamma_n\eta_{n+1},\qquad v_n\in\partial f(x_n),
--   $$
--   with $c_1/n^\alpha\le\gamma_n\le c_2/n^\alpha$ for $n\ge1$ and some $\alpha\in(1/2,1]$. Let $x^*$ be an active strict saddle of order 5 satisfying the Verdier and angle conditions, with active manifold $M$, and let the noise satisfy, almost surely on $[x_n\to x^*]$, Assumption 3: conditional mean zero, $\limsup\mathbb E[\|\eta_{n+1}\|^4\mid\mathcal F_n]<\infty$ and $\liminf\mathbb E[\|\eta^-_{n+1}\|\mid\mathcal F_n]>0$. Then
--   $$
--   \mathbb P(x_n\to x^*)=0.
--   $$
--
--   This is the main result of the paper: the explicit stochastic subgradient method, on a nonsmooth nonconvex function, avoids active strict saddles. Weak convexity is not assumed; the angle condition stands in for it.
--
--   **Formalization Note** $M$, its dimension, $F$, $G$, $w$, $U$ and the constants are parameters of the theorem, so that Assumption 3 speaks of the same $M$. No integrability of $\eta$ and no boundedness of $(x_n)$ is assumed.
--
--   Differences from the source:
--   - reading: $\mathbb E[\eta_{n+1}\mid\mathcal F_n]$, printed without integrability → the generalized conditional expectation: `condLExp` for moments, and truncation to $\{\mathbb E[\|\eta_{n+1}\|\mid\mathcal F_n]\le K\}$ for the mean; reason: Assumption 3 is local to an event and Corollary 1 localizes the moments, so global integrability would be a special case, and Mathlib's `condExp` alone would be vacuous
--   - generalization: "for all $n$" in Assumption 3 i), which presupposes the mean at each $n$ → the clause applies where $\mathbb E[\|\eta_{n+1}\|\mid\mathcal F_n]$ is finite; reason: a weaker hypothesis; by ii) it is finite for all large $n$, which is all the proof uses
--   - generalization: Definition 1, absolutely continuous curves on $(0,1)$ → published `IsPathDifferentiable`, Lipschitz curves on $\mathbb R$; reason: Definition 1 implies it, by restricting a Lipschitz curve to unit intervals, so the hypothesis is weaker
--   - encoding: closed convex hull in $\partial f$ → published `clarkeSubdiff`, the convex hull of `almostGradients`; reason: for locally Lipschitz $f$ the limiting gradients are compact, so the hull is closed; same set
--   - encoding: sharpness $\inf\{\|v\|\}>0$ → a constant $c>0$ below every $\|v\|$; reason: the set may be empty ($M=\mathbb R^d$, p.9); same instances
--   - encoding: the set $P_M(x)$ → the angle condition for every nearest point $z$ (`IsMetricProjection`); reason: it is a singleton near $x^*$ by Lemma 1; same instances
--   - encoding: smooth representative $F$ and extension $G$ of $\nabla_M f$, "any" choice → explicit data of Assumption 2, on one open $U$; reason: the values do not depend on the choice (p.5) and each condition passes to smaller neighbourhoods; same instances
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Theorem 3, p.12

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSaddleSGD_ManifoldCalculus
import Definitions.Def_ActiveSaddleSGD_ActiveManifold
import Definitions.Def_ActiveSaddleSGD_Algorithm
import Definitions.Def_ActiveSaddleSGD_Noise
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates

open ProjLikeRetr.Retractor MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Theorem 3, p.12: let Assumptions 1–3 hold. Then
`ℙ(x_n → x*) = 0`: the iterates (10) of the stochastic subgradient method almost surely do not
converge to an active strict saddle of order 5 satisfying the Verdier and angle conditions.

**Formalization Note** The active manifold `M`, its dimension `k`, the representative `F`, the
extension `G`, the direction `w`, the neighbourhood `U` and the constants are parameters: this is
"`∃ M …` ⟹ conclusion", with Assumption 3 speaking of the same `M`, through
`E⁻ = negEigenspace (curvOp M G xs)`. No integrability of the noise and no boundedness of the
iterates is assumed; the noise conditions hold only almost surely on `[x_n → x*]`. -/
theorem theorem_3 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA3 : Assumption3 μ ℱ x η xs (negEigenspace (curvOp M G xs))) :
    μ {ω | Tendsto (fun n => x n ω) atTop (𝓝 xs)} = 0 := by sorry

end ActiveSaddleSGD
