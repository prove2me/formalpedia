-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_comp_rotation_of_mem_embeddedFastPlaneSet
-- name    : FiniteEnergyPlane.eq_comp_rotation_of_mem_embeddedFastPlaneSet
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:47:16.421738+00:00
-- url     : https://prove2.me/theorems/db984267-b2ba-4b76-9b23-ea65cdd20f18
-- title:
--   Planes in $\Lambda(\{y_0\},P)$ differ by a rotation of the domain
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $y_0\in\mathbb{R}^4$, $\gamma\in\mathbb{R}$ and $u,v\in\Lambda(\{y_0\},P)$. Then there is $\theta\in\mathbb{R}$ with $u(e^{i\theta}z)=v(z)$ for all $z\in\mathbb{C}$.
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`, whose members satisfy $u(0)=y_0$ and have $d\lambda$-energy $\gamma$ on $\{|z|>1\}$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.1

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.1. Let `P` be a periodic Reeb orbit of Conley–Zehnder index
at least `3` and `y₀ ∈ V 1`. Two planes in `Λ({y₀}, P)` differ by a rotation of the domain: there
is `θ ∈ ℝ` with `u(e^{iθ} z) = v(z)` for every `z`. -/
theorem eq_comp_rotation_of_mem_embeddedFastPlaneSet (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y₀ : V 1) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P {y₀} γ) (hv : v ∈ embeddedFastPlaneSet H J P {y₀} γ) :
    ∃ θ : ℝ, ∀ z, u (Complex.exp ((θ : ℂ) * Complex.I) * z) = v z := by
  sorry

end FiniteEnergyPlane
