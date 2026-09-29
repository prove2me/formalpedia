-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_tendsto_infDist_div_of_flowInvariant
-- name    : ClarkeGradients.FlowInvariance.tendsto_infDist_div_of_flowInvariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:51:10.536004+00:00
-- url     : https://prove2.me/theorems/9a23612c-b1f1-410a-8b56-79968384b767
-- title:
--   Proof of Theorem (4.4), Eq. (4.9) — flow-invariance gives d_F(y + δv)/δ → 0
-- statement:
--   Let $X$ be a Lipschitz multifunction (4.2) from $\mathbb R^n$ to $\mathbb R^n$ whose values are nonempty and compact, and let $F$ be a nonempty closed subset of $\mathbb R^n$ that is flow-invariant for $X$ (4.3). Then for every $y\in F$ and every $v\in X(y)$,
--
--   $$
--   \lim_{\delta\downarrow 0}\frac{d_F(y+\delta v)}{\delta}=0.
--   $$
--
--   Every admissible velocity at a point of $F$ is thus a direction along which $F$ is approached to first order. This is the step (1) $\Rightarrow$ (4.9) of the proof of Theorem (4.4), which combined with Proposition (3.7) gives (1) $\Rightarrow$ (2); it is also the implication used in the proof of Corollary (4.12).
--
--   **Formalization Note** The paper writes the conclusion as $\limsup_{\delta\downarrow 0} d_F(y+\delta v)/\delta=0$; since the quotient is nonnegative this is equivalent to convergence to $0$, stated with `Tendsto` along `𝓝[>] 0` (so $\delta=0$ is excluded). The paper's argument uses a trajectory $x$ with $x(0)=y$ and $\dot x(0)=v$, whose existence is Filippov's theorem [7, Theorem 5]; that existence result is part of the proof burden and is not a hypothesis here.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 261, proof of Theorem (4.4), Eq. (4.9)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_IsLipschitzMultifunction
import Definitions.Def_ClarkeGradients_FlowInvariance_FlowInvariant

open Filter Topology

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), proof of Theorem (4.4), limit (4.9). Let `X` be a Lipschitz multifunction
(4.2) with nonempty compact values, and let `F ⊆ ℝⁿ` be nonempty, closed and flow-invariant for
`X` (4.3). Then for every `y ∈ F` and every `v ∈ X(y)`,
`d_F(y + δv)/δ → 0` as `δ ↓ 0`. -/
theorem tendsto_infDist_div_of_flowInvariant {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F)
    (hinv : FlowInvariant X F) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ F)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ X y) :
    Tendsto (fun δ : ℝ => Metric.infDist (y + δ • v) F / δ) (𝓝[>] 0) (𝓝 0) := by sorry

end ClarkeGradients.FlowInvariance
