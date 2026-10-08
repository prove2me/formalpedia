-- Prove2me | Theorems.Thm_BanditGD_Regret_smoothed_regret
-- name    : BanditGD.Regret.smoothed_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:28:31.878323+00:00
-- url     : https://prove2.me/theorems/aba088bf-67b5-4baa-9e6d-2949bcef5ff8
-- title:
--   Proof of Theorem 1, p. 9 — expected regret of BGD against the smoothed costs ĉₜ on (1−α)S is ≤ RdC√n/δ
-- statement:
--   **Setting** (§1.2, §1.4). Let $d\ge1$ and let $S\subseteq\mathbb R^d$ be closed and convex with $r\mathbb B\subseteq S\subseteq R\mathbb B$, $r>0$. Let $C>0$ and let $c_1,c_2,\dots:\mathbb R^d\to\mathbb R$ be a fixed (oblivious) sequence of functions, each convex on $S$ with $|c_t(x)|\le C$ for $x\in S$. On a probability space let $u_1,u_2,\dots$ be independent random vectors, each uniformly distributed on the unit sphere $\mathbb S$, and let $y_1,y_2,\dots$ be the run of $\mathrm{BGD}(\alpha,\delta,\nu)$ driven by them (for every outcome).
--
--   Let $n\ge1$, $\nu=R/(C\sqrt n)$, $\alpha\le1$, and $0<\delta<\alpha r$. Write $\hat c_t(x)=\mathbb E_{v\in\mathbb B}[c_t(x+\delta v)]$ for the smoothed costs. Then
--   $$\mathbb E\Big[\sum_{t=1}^n\hat c_t(y_t)\Big]-\min_{x\in(1-\alpha)S}\sum_{t=1}^n\hat c_t(x)\le\frac{RdC\sqrt n}{\delta}.$$
--
--   This is the step of the paper's proof in which BGD is recognised as the expected gradient descent of Lemma 2 run on the smoothed costs over $(1-\alpha)S$, with gradient estimates of norm at most $G=dC/\delta$.
--
--   **Formalization Note** Independence of the directions is required (the paper's "select unit vector $u_t$ uniformly at random" at each period); it is what makes $u_t$ independent of $y_t$. The set $S$ is assumed closed so that the projections of Figure 1 exist. The paper's condition $\delta/r\le\alpha$ is strengthened to the strict $\delta<\alpha r$, which keeps every smoothing ball $y+\delta\mathbb B$, $y\in(1-\alpha)S$, inside the interior of $S$, where the convex costs are continuous; Theorem 1's parameters satisfy it. The paper's $\alpha<1$ is relaxed to $\alpha\le1$. The minimum is an infimum over $(1-\alpha)S$. Nothing is assumed about $c_t$ outside $S$.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 9, proof of Theorem 1 (first display on p. 9)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
open MeasureTheory
open scoped Pointwise

namespace BanditGD.Regret

theorem smoothed_regret {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : 1 ≤ n) (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : 0 < δ) (hδα : δ < α * r) (hα1 : α ≤ 1)
    (hrun : ∀ ω, IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret ((1 - α) • S)
        (fun t => RegretBandits.Nonlinear.smoothedLoss d δ (c t)) P y n
      ≤ R * d * C * Real.sqrt n / δ := by sorry

end BanditGD.Regret
