-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_hasDerivAt_infDist_trajectory_le
-- name    : ClarkeGradients.FlowInvariance.hasDerivAt_infDist_trajectory_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:49:10.713994+00:00
-- url     : https://prove2.me/theorems/62eeecfb-4459-4d82-b790-e74e549c4d41
-- title:
--   Proof of Theorem (4.4), Eq. (4.8) — f′(t) ≤ K f(t) for f(t) = d_F(x(t))
-- statement:
--   Let $X$ be a multifunction from $\mathbb R^n$ to $\mathbb R^n$ whose values $X(x)$ are nonempty and compact, and suppose $X$ satisfies the Lipschitz condition (4.2) with constant $K$: for all $x_1,x_2$ and $v_1\in X(x_1)$ there is $v_2\in X(x_2)$ with $|v_1-v_2|\le K|x_1-x_2|$. Let $F$ be a nonempty closed subset of $\mathbb R^n$ such that $X(y)\subseteq T_F(y)$ for every $y\in F$ (condition (2) of Theorem (4.4)). Let $x$ be a trajectory (4.1) for $X$ with $x(0)\in F$, and define $f(t)=d_F(x(t))$. Then for almost every $t\in[0,1]$: if $f$ is differentiable at $t$, then
--
--   $$
--   f'(t)\le K\,f(t).
--   $$
--
--   This differential inequality, together with $f(0)=0$ and $f\ge 0$, yields $f\equiv 0$ on $[0,1]$ by a Gronwall-type argument, which is the implication (2) $\Rightarrow$ (1) of Theorem (4.4).
--
--   **Formalization Note** $K$ is passed explicitly together with the Lipschitz condition it satisfies, since the conclusion refers to it. The conclusion is quantified over every derivative value $d$ of $t\mapsto d_F(x(t))$ at $t$ (`HasDerivAt … d t → d ≤ K * infDist (x t) F`), for almost every $t$ with respect to Lebesgue measure on $[0,1]$; it does not assert that $f$ is differentiable. The hypothesis $x(0)\in F$ belongs to the setting of the paper's argument. Nonempty compact values are the standing assumption of §4 (p. 259).
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), pp. 260–261, proof of Theorem (4.4), Eq. (4.8)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone
import Definitions.Def_ClarkeGradients_FlowInvariance_IsTrajectory

open MeasureTheory

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), proof of Theorem (4.4), inequality (4.8). Let `X` have nonempty compact values
and satisfy the Lipschitz condition (4.2) with constant `K`, let `F ⊆ ℝⁿ` be nonempty and closed,
and assume (2) of Theorem (4.4): `X(y) ⊆ T_F(y)` for every `y ∈ F`. Let `x` be a trajectory for `X`
with `x(0) ∈ F`, and `f(t) = d_F(x(t))`. Then for almost every `t ∈ [0, 1]`, whenever `f` is
differentiable at `t`, `f'(t) ≤ K f(t)`. -/
theorem hasDerivAt_infDist_trajectory_le {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (K : ℝ)
    (hK : ∀ x₁ x₂ : EuclideanSpace ℝ (Fin n), ∀ v₁ ∈ X x₁, ∃ v₂ ∈ X x₂,
      ‖v₁ - v₂‖ ≤ K * ‖x₁ - x₂‖)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (htan : ∀ y ∈ F, X y ⊆ tangentCone F y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : IsTrajectory X x) (hx0 : x 0 ∈ F) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ d : ℝ,
      HasDerivAt (fun s => Metric.infDist (x s) F) d t →
        d ≤ K * Metric.infDist (x t) F := by sorry

end ClarkeGradients.FlowInvariance
