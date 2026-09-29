-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_mem_tangentCone_iff
-- name    : ClarkeGradients.FlowInvariance.mem_tangentCone_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:52:15.812964+00:00
-- url     : https://prove2.me/theorems/634fbc4a-8ed2-4215-8fe3-93beab2e0c77
-- title:
--   Proposition (3.7) — tangency via liminf of d_E(e + δv)/δ
-- statement:
--   Let $E$ be a nonempty closed subset of $\mathbb R^n$, $e_0\in E$ and $v\in\mathbb R^n$. The following are equivalent:
--
--   1. $v\in T_E(e_0)$;
--   2. $$\lim_{e\to e_0,\ e\in E}\ \liminf_{\delta\downarrow 0}\frac{d_E(e+\delta v)}{\delta}=0.$$
--
--   This gives an alternate characterization of Clarke tangents that involves only the distance function along rays from points of $E$ near $e_0$. It closes the implication (1) $\Rightarrow$ (2) in the proof of Theorem (4.4).
--
--   **Formalization Note** The outer limit is taken along `𝓝[E] e₀`, i.e. $e\to e_0$ with $e\in E$, and $e=e_0$ is *not* excluded: at an isolated point of $E$ the punctured filter would be trivial and would make (2) hold for every $v$, while $T_E(e_0)=\{0\}$ there. For $e\in E$ and $\delta>0$ the inner quotient lies in $[0,|v|]$, so the real `liminf` along `𝓝[>] 0` is a genuine lower limit, not a junk value. "lim … = 0" is `Tendsto … (𝓝 0)`.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 256, Proposition (3.7)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone

open Filter Topology

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Proposition (3.7): let `E ⊆ ℝⁿ` be nonempty and closed, `e₀ ∈ E` and
`v ∈ ℝⁿ`. Then `v ∈ T_E(e₀)` if and only if
`lim_{e → e₀, e ∈ E} liminf_{δ ↓ 0} d_E(e + δv)/δ = 0`. -/
theorem mem_tangentCone_iff {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : E.Nonempty) (hEc : IsClosed E) (e₀ : EuclideanSpace ℝ (Fin n)) (he₀ : e₀ ∈ E)
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ tangentCone E e₀ ↔
      Tendsto (fun e => liminf (fun δ : ℝ => Metric.infDist (e + δ • v) E / δ) (𝓝[>] 0))
        (𝓝[E] e₀) (𝓝 0) := by sorry

end ClarkeGradients.FlowInvariance
