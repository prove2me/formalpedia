-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_2
-- name    : ActiveSaddleSGD.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:04.340432+00:00
-- url     : https://prove2.me/theorems/c364ff92-d0ee-4c0a-a956-0b2bb9d7cfa2
-- title:
--   Lemma 2 — $F\circ P_M$ is $C^4$, its gradient on $M$ is $\nabla_Mf$, and the Hessians agree on $T_{x^*}M$
-- statement:
--   Let Assumption 2 hold, let $r>0$ be such that $P_M$ is well defined and $C^4$ on $B(x^*,r)$, and let $F$ be a $C^5$ representative of $f$ on $M$ on an open set $U$ into which $P_M$ maps $B(x^*,r)$. Then $F\circ P_M$ is $C^4$ on $B(x^*,r)$, for $y\in M\cap B(x^*,r)$,
--   $$
--   \nabla(F\circ P_M)(y)=\nabla_Mf(y),
--   $$
--   and for $w\in T_{x^*}M$,
--   $$
--   \langle w,\mathcal H_{f,M}(x^*)(w)\rangle=\langle w,\mathcal H_{F\circ P_M}(x^*)w\rangle,
--   $$
--   where $\mathcal H_{F\circ P_M}(x^*)$ is the Euclidean Hessian.
--
--   This supplies the smooth field $D=\nabla(F\circ P_M)$ whose linearization at $x^*$ carries the negative curvature.
--
--   **Formalization Note** The Euclidean Hessian is the derivative of the gradient, and $\mathcal H_{f,M}$ on $T_{x^*}M$ is `curvOp`.
--
--   Differences from the source:
--   - reading: $F:B(0,r)\to\mathbb R$ → $F$ is the representative of Assumption 2, on $U$, and $P_M$ maps $B(x^*,r)$ into $U$; reason: $F\circ P_M$ needs $F$ on $P_M(B(0,r))$, which need not lie in $B(0,r)$ on a curved $M$, so the page's domain of $F$ is read as a neighbourhood of $P_M(B(0,r))$; this is the least the composition requires
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 2, p.17

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

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 2, p.17: under Assumption 2, if `P_M` is
well defined and `C⁴` on `B(x*, r)` and `F` is a `C⁵` representative of `f`, then `F ∘ P_M` is `C⁴`
on `B(x*, r)`, `∇(F ∘ P_M)(y) = ∇_M f(y)` for `y ∈ M ∩ B(x*, r)`, and
`⟨w, H_{f,M}(x*)(w)⟩ = ⟨w, H_{F∘P_M}(x*) w⟩` for `w ∈ T_{x*}M`.

**Formalization Note** `x*` is general where the page has `0`. `F` is the representative of
Assumption 2, on `U`. The page has `F : B(0, r) → ℝ`, but `F ∘ P_M` needs `F` on `P_M(B(0, r))`, which
need not lie in `B(x*, r)`; so `P_M` is required to map `B(x*, r)` into `U`, the domain of `F`. The Euclidean Hessian is the derivative of the gradient. -/
theorem lemma_2 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (r : ℝ) (hr : 0 < r)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : IsProjectionOn M P xs r) (hU : Set.MapsTo P (Metric.ball xs r) U) :
    ContDiffOn ℝ 4 (F ∘ P) (Metric.ball xs r) ∧
      (∀ y ∈ M ∩ Metric.ball xs r, gradient (F ∘ P) y = riemGrad M F y) ∧
      ∀ u ∈ tangentSpace M xs,
        ⟪u, curvOp M G xs u⟫_ℝ = ⟪u, fderiv ℝ (gradient (F ∘ P)) xs u⟫_ℝ := by sorry

end ActiveSaddleSGD
