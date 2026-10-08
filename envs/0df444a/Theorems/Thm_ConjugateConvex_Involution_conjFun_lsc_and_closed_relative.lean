-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_conjFun_lsc_and_closed_relative
-- name    : ConjugateConvex.Involution.conjFun_lsc_and_closed_relative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:31.314705+00:00
-- url     : https://prove2.me/theorems/174d6fe6-3d08-4156-b193-df89d564deb1
-- title:
--   §3, p. 76 — φ is semi-continuous from below and Γ is closed relative to φ
-- statement:
--   Let $G \subseteq \mathbb R^n$, let $f$ be a real function defined in $G$, and let $(\Gamma, \varphi)$ be its conjugate pair. Then
--
--   1. $\varphi$ is semi-continuous from below on $\Gamma$: for every $\xi^* \in \Gamma$,
--   $$
--   \liminf_{\xi \to \xi^*,\ \xi \in \Gamma} \varphi(\xi) \ge \varphi(\xi^*);
--   $$
--   2. $\Gamma$ is closed relative to $\varphi$: at every boundary point $\xi^*$ of $\Gamma$ that does not belong to $\Gamma$, $\varphi(\xi) \to +\infty$ as $\xi \to \xi^*$ within $\Gamma$.
--
--   Together with the convexity of $\Gamma$ and $\varphi$ and the nonemptiness of $\Gamma$, this shows that $(\Gamma, \varphi)$ has the same properties as $(G, f)$.
--
--   **Formalization Note** Semi-continuity is `LowerSemicontinuousOn φ Γ`; the boundary points of $\Gamma$ not in $\Gamma$ are the points of `closure Γ \ Γ`, and the limit is taken along `𝓝[Γ] ξ*`. No hypothesis on $(G, f)$ is assumed; both parts hold for every $G$ and $f$, which is stronger than the paper's setting.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 76, §3 ('Let now ξ* be a boundary point of Γ … i.e. that φ(ξ) is semi-continuous from below')

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
open Filter Topology

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 76: `φ` is semi-continuous from below on `Γ`, and `Γ` is closed
relative to `φ`: at every boundary point `ξ*` of `Γ` not in `Γ`, `φ(ξ) → ∞` as `ξ → ξ*` in `Γ`. -/
theorem conjFun_lsc_and_closed_relative {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    LowerSemicontinuousOn (conjFun G f) (conjDomain G f) ∧
      ∀ ξ ∈ closure (conjDomain G f) \ conjDomain G f,
        Tendsto (conjFun G f) (𝓝[conjDomain G f] ξ) atTop := by sorry

end ConjugateConvex.Involution
