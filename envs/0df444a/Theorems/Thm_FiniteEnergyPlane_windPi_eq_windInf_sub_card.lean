-- Prove2me | Theorems.Thm_FiniteEnergyPlane_windPi_eq_windInf_sub_card
-- name    : FiniteEnergyPlane.windPi_eq_windInf_sub_card
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-01T15:39:23.005197+00:00
-- url     : https://prove2.me/theorems/720d7b95-35b6-4e71-b5c4-37bd135bd00e
-- title:
--   The Hofer–Wysocki–Zehnder identity $\mathrm{wind}_\pi=\mathrm{wind}_\infty-\chi+\#\Gamma$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $\Gamma\subset\mathbb{C}$ be finite and $u$ a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ such that $\infty$ is a positive puncture and every $z\in\Gamma$ a negative puncture, all nondegenerate in the sense of Hryniewicz, Definition 2.9, and suppose $\pi\,du$ does not vanish identically. Then $\mathrm{wind}_\pi(u)$, $\mathrm{wind}_\infty(u,\infty)$ and $\mathrm{wind}_\infty(u,z)$ for $z\in\Gamma$ are defined, and
--   $$\mathrm{wind}_\pi(u)=\mathrm{wind}_\infty(u,\infty)-\sum_{z\in\Gamma}\mathrm{wind}_\infty(u,z)-\chi(S^2)+\#(\Gamma\cup\{\infty\}).$$
--
--   **Formalization Note** The punctures are `IsNondegenerateEnd H u cylInf P∞ 1` and `IsNondegenerateEnd H u (cylEndAt z) P_z (-1)` for $z\in\Gamma$; \"$\pi\,du\not\equiv0$\" is `∃ z ∉ Γ, piDs H u z ≠ 0`. In Lean the right-hand side is `kinf - ∑ z ∈ Γ, kz z - 2 + (Γ.card + 1)`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.15; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 3.19; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer–Wysocki–Zehnder: Hryniewicz, Lemma 2.15 (Hryniewicz, Trans. AMS 2012, Lemma 3.19), for
`S = ℂ ∪ {∞}`. Let `u` be a finite-energy `J̃`-holomorphic curve on `ℂ \ Γ`, `Γ` finite, with a
positive puncture at `∞`, negative punctures at the points of `Γ`, all nondegenerate in the sense of
Definition 2.9, and with `π du` not identically zero. Then `wind_π(u)` and the asymptotic windings
are defined, and `wind_π(u) = wind_∞(u, ∞) - Σ_{z ∈ Γ} wind_∞(u, z) - χ(S²) + #(Γ ∪ {∞})`. -/
theorem windPi_eq_windInf_sub_card (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    ∃ (kinf : ℤ) (kz : ℂ → ℤ) (kπ : ℤ), HasWindInfAt H u cylInf 1 kinf ∧
      (∀ z ∈ Γ, HasWindInfAt H u (cylEndAt z) (-1) (kz z)) ∧ HasWindPi H u Γ kπ ∧
      kπ = kinf - ∑ z ∈ Γ, kz z - 2 + (Γ.card + 1) := by
  sorry

end FiniteEnergyPlane
