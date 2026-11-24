-- Prove2me | Theorems.Thm_Curvature_minimaxWidth
-- name    : Curvature.minimaxWidth
-- status  : Open
-- author  : @ssakaue
-- created : 2026-11-24T07:30:05.002948+00:00
-- url     : https://prove2.me/theorems/1dfc080e-a34c-4606-a5d7-c4ade7b6c7fc
-- title:
--   Theorem 21 — minimax small-loss regret on standard domains
-- statement:
--   Let $d\ge1$, and let $\mathcal K\subseteq\mathbb R^d$ be one of the following sets:
--
--   - a unit ball $\mathbb B_p^d=\{x\in\mathbb R^d:\lVert x\rVert_p\le1\}$ with $1\le p\le\infty$,
--   - a Euclidean ball $R\mathbb B_2^d$ with $R>0$,
--   - an ellipsoid $w_\circ+U\operatorname{diag}(a)\mathbb B_2^r$ or a box $w_\circ+U\operatorname{diag}(a)\mathbb B_\infty^r$, where $1\le r\le d$, $w_\circ\in\mathbb R^d$, $U\in\mathbb R^{d\times r}$ satisfies $U^\top U=I_r$, and $a\in(0,\infty)^r$, or
--   - the probability simplex $\triangle_d=\{w\in[0,\infty)^d:\sum_{i=1}^dw_i=1\}$ with $d\ge2$.
--
--   Fix $G>0$ and $b\ge0$, and consider the following game between a learner and an environment, which draw independent private random seeds. The learner knows $\mathcal K$, $G$ and $b$ but not the horizon. In each round $t=1,2,\ldots$, the learner chooses $w_t\in\mathcal K$ from its seed and the loss functions $f_1,\ldots,f_{t-1}$ of the earlier rounds, and then the environment, from its own seed, the history and $w_t$, chooses a convex loss $f_t\colon\mathbb R^d\to\mathbb R$ that is $G$-Lipschitz with respect to $\lVert\cdot\rVert_2$. After $T$ rounds, the minimum of the shifted comparator loss and the regret against the best fixed comparator are
--
--   $$
--   \Delta_T^\star\coloneqq\min_{u\in\mathcal K}\sum_{t=1}^T\Bigl(f_t(u)-\min_{w\in\mathcal K}f_t(w)\Bigr)
--   \quad\text{and}\quad
--   \sum_{t=1}^Tf_t(w_t)-\min_{u\in\mathcal K}\sum_{t=1}^Tf_t(u).
--   $$
--
--   An environment respects the **comparator-loss budget** $b$ at horizon $T$ if $\Delta_T^\star\le b$ on every realization. The minimax value $R_\infty^\star(\mathcal K,G,b)$ is the infimum over learners of the supremum, over horizons $T\ge1$ and environments that respect the budget at $T$, of the expected regret against the best fixed comparator, where the expectation is taken over both seeds. For each fixed history of losses, the learner's prediction is a measurable function of its seed. For each admissible environment, the realized regret is almost everywhere strongly measurable under the product law of the two seeds.
--
--   Let $\omega_{\psi_1}(\mathcal K)$ be the maximal subexponential mean width defined in the mission description, and write $S_{\mathcal K}\coloneqq G\,\omega_{\psi_1}(\mathcal K)$. Then
--
--   $$
--   R_\infty^\star(\mathcal K,G,b)=\Theta\bigl(S_{\mathcal K}+\sqrt{S_{\mathcal K}b}\bigr),
--   $$
--
--   where the two multiplicative factors implicit in $\Theta$ are positive universal constants, independent of $d$, $r$, $p$, $\mathcal K$, $G$ and $b$. The two bounds hold in the following stronger forms.
--
--   1. **Upper bound.** A single deterministic strategy, independent of $b$, computes $w_t$ using only one feedback vector $g_s$ from each earlier round $s<t$. Each $g_s$ may be any vector of Euclidean norm at most $G$ that satisfies the subgradient inequality for $f_s$ at $w_s$ on $\mathcal K$. For every $b\ge0$ and $T\ge1$, its regret against the best fixed comparator is at most a universal constant times $S_{\mathcal K}+\sqrt{S_{\mathcal K}b}$ on every realization with $\Delta_T^\star\le b$, and hence also in expectation.
--   2. **Lower bound.** For each randomized learner, there are a horizon $T\ge1$ and a deterministic sequence of convex $G$-Lipschitz losses $f_1,\ldots,f_T$ with $\Delta_T^\star\le b$, fixed before the learner's random seed is drawn, on which the learner's expected regret against the best fixed comparator is at least a universal constant times $S_{\mathcal K}+\sqrt{S_{\mathcal K}b}$. Such a sequence is one environment of the game, so this lower bound applies to the minimax value.
--
--   The matching bounds are claimed only for the sets listed above.
-- source:
--   arXiv:2611.27572v1, Theorem 21, p. 58. https://arxiv.org/html/2611.27572v1#Thmtheorem21

import Definitions.Def_Curvature_MinimaxGame
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
open Curvature
open MeasureTheory
universe u v
open scoped BigOperators NNReal
variable {d : ℕ}

theorem Curvature.minimaxWidth {K : Set (Sparse.Space d)} (hK : CanonicalDomain d K) (G : ℝ≥0) (hG : 0<G)
    (b : ℝ) (hb : 0≤b) :
    let W := (G:ℝ)*subexponentialWidth K
    let rate := W+Real.sqrt (W*b)
    ((rate/20480 : ℝ) : EReal) ≤ minimaxValue.{u,v} K G b ∧
      minimaxValue.{u,v} K G b ≤ ((adaptiveWidthConstant*rate : ℝ):EReal) ∧
      OneSubgradientUpper K G adaptiveWidthConstant ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (L : FullInfoLearner (Sparse.Space d) Ω K)
        (μ : Measure Ω) [IsProbabilityMeasure μ], L.HasHardSequence μ G b (rate/20480) := by sorry
