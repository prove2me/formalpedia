-- Prove2me | Theorems.Thm_CoherentSDDP_Inner_Qhat_convex
-- name    : CoherentSDDP.Inner.Qhat_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:13.216893+00:00
-- url     : https://prove2.me/theorems/43c0a30a-e755-4a7b-bde1-9f5cc194c51c
-- title:
--   §3.2, pp. 7–8 — 𝒬̂ₛ is the lower boundary of the convex hull ℋ of the points, and ℋ lies in the epigraph of every convex function below the bounds
-- statement:
--   In the setting of the model file, fix a stage $s\le T$, points $x^1_{s-1},\dots,x^{J}_{s-1}\in\mathbb R^n$ and bounds $q^1_s,\dots,q^J_s\in\mathbb R\cup\{+\infty\}$ (none equal to $-\infty$), and let
--   $$
--   \hat{\mathcal Q}_s(x)=\min\Big\{\sum_{j}\lambda^jq^j_s:\ \sum_j\lambda^jx^j_{s-1}=x,\ \lambda\in\Lambda_{s-1}\Big\}.
--   $$
--   Then:
--
--   1. $\hat{\mathcal Q}_s$ is the lower boundary of the convex hull $\mathcal H$ of the points $(x^j_{s-1},q^j_s)$: its epigraph $\{(x,r)\in\mathbb R^n\times\mathbb R:\hat{\mathcal Q}_s(x)\le r\}$ equals the convex hull of the vertical half-lines $\{(x^j_{s-1},r): r\ge q^j_s\}$, that is, $\mathcal H+(\{0\}\times[0,\infty))$;
--   2. $\hat{\mathcal Q}_s$ is convex (its epigraph is convex);
--   3. $\hat{\mathcal Q}_s(x^j_{s-1})\le q^j_s$ for every $j$;
--   4. $\mathcal H$ lies in the epigraph of every convex function below the bounds: if $F:\mathbb R^n\to\mathbb R\cup\{\pm\infty\}$ is convex and $F(x^j_{s-1})\le q^j_s$ for every $j$, then
--   $$
--   F(x)\le\hat{\mathcal Q}_s(x)\qquad\text{for every }x.
--   $$
--
--   Part 4 is the page's "the convex hull $\mathcal H$ … is a subset of the convex epigraph of $\mathbb E[Q_{t+1}(x_t,\omega_{t+1})]$" for an arbitrary convex function in place of $\mathbb E[Q_{t+1}]$, under the page's hypothesis that the $q^j$ bound it at the points; this is what makes $\hat{\mathcal Q}_s$ an inner (upper bound) approximation.
--
--   **Formalization Note** The true value function $Q_{t+1}$ is not defined in this mission, so part 4 is stated for every convex $F$ bounded by the $q^j$ at the points, which contains the page's case $F=\mathbb E[Q_{t+1}]$. Points whose bound is $+\infty$ contribute no point to $\mathcal H$ (their half-line is empty). The page says $\hat{\mathcal Q}_t(x^j_{t-1})=q^j_t$ (p. 11); that holds only for points on the lower envelope, so $\le$ is stated. The hypothesis $s\le T$ excludes the terminal stage, where $\hat{\mathcal Q}_{T+1}\equiv0$ by convention and is unrelated to the bounds. The hypothesis $q^j_s\neq-\infty$ reflects that the bounds are upper bounds on costs; it follows from the upper-bound hypothesis of the goal theorem.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), pp. 7–8, §3.2, the convex hull ℋ, Λ_t and 𝒬̂_{t+1}; p. 11, 𝒬̂_t(x^j_{t−1}) = q^j_t

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace CoherentSDDP.Inner

theorem Qhat_convex {n m : ℕ} {Ω : ℕ → Type} (M : Model n m Ω) (D : InnerData n) (s : ℕ)
    (hsT : s ≤ M.T) (hqv : ∀ j, D.qv s j ≠ ⊥) :
    {q : (Fin n → ℝ) × ℝ | Qhat M D s q.1 ≤ (q.2 : EReal)} =
        convexHull ℝ {q : (Fin n → ℝ) × ℝ | ∃ j, q.1 = D.pts s j ∧ D.qv s j ≤ (q.2 : EReal)} ∧
      EConvex (Qhat M D s) ∧
      (∀ j, Qhat M D s (D.pts s j) ≤ D.qv s j) ∧
      ∀ F : (Fin n → ℝ) → EReal, EConvex F → (∀ j, F (D.pts s j) ≤ D.qv s j) →
        ∀ x, F x ≤ Qhat M D s x := by sorry

end CoherentSDDP.Inner
