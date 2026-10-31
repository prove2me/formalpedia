-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_3
-- name    : ActiveSaddleSGD.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:00.357974+00:00
-- url     : https://prove2.me/theorems/a47c93a3-64d7-4c68-a302-e5716297608d
-- title:
--   Lemma 3 — first-order expansion of $P_M$ with remainders $R_1$, $R_2$
-- statement:
--   Let Assumption 2 hold and let $P_M$ be single-valued and $C^4$ near $x^*$. For $r$ small enough there is $C>0$ such that for $x,x'\in B(x^*,r)$, with $y'=P_M(x')$ and $y=P_M(x)$,
--   $$
--   y'-y=J_{P_M}(y)(x'-x)+R_1(x,x',y)+R_2(x,x'),
--   $$
--   where $\|R_1(x,x',y)\|\le C\|x'-x\|\|x-y\|$ and $\|R_2(x,x')\|\le C\|x'-x\|^2$.
--
--   This is the Taylor step that turns (10) into a recursion for $P_M(x_n)$.
--
--   Differences from the source:
--   - encoding: open or closed $B(0,r)$ → closed ball; reason: the iterates satisfy $\|x_n\|\le r$ on $[n<\tau_N]$, and $r$ is free; the closed ball of radius $r$ lies in the open ball of radius $2r$
--   - encoding: functions $R_1(x,x',y)$, $R_2(x,x')$ → vectors $R_1,R_2$ chosen for each pair $(x,x')$; reason: $y$ is a function of $x$; same content
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 3, p.19

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

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 3, p.19: for `r` small enough there is
`C > 0` such that for `x, x′ ∈ B(x*, r)`, `y′ − y = J_{P_M}(y)(x′ − x) + R₁(x, x′, y) + R₂(x, x′)`
with `y′, y = P_M(x′), P_M(x)`, `‖R₁‖ ≤ C ‖x′ − x‖ ‖x − y‖` and `‖R₂‖ ≤ C ‖x′ − x‖²`.

**Formalization Note** The ball is closed, as the iterates satisfy `‖x_n‖ ≤ r` on `[n < τ_N]`.
`R₁`, `R₂` are chosen for each pair `(x, x′)`: `y` is a function of `x`, so this is the same as
functions of `(x, x′, y)` and `(x, x′)`. `r₀` is the radius on which the projection is known; `x*`
is general where the page has `0`. -/
theorem lemma_3 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hP : IsProjectionOn M P xs r₀) :
    ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∃ C > 0,
      ∀ x ∈ Metric.closedBall xs r, ∀ x' ∈ Metric.closedBall xs r,
        ∃ R₁ R₂ : EuclideanSpace ℝ (Fin d),
          P x' - P x = fderiv ℝ P (P x) (x' - x) + R₁ + R₂ ∧
            ‖R₁‖ ≤ C * ‖x' - x‖ * ‖x - P x‖ ∧ ‖R₂‖ ≤ C * ‖x' - x‖ ^ 2 := by sorry

end ActiveSaddleSGD
