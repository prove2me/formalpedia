-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_comp_add_smul
-- name    : FiniteEnergyPlane.isFastPlane_comp_add_smul
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-22T19:27:22.607727+00:00
-- url     : https://prove2.me/theorems/52d4a747-7181-45d5-837d-cbb46ddb1897
-- title:
--   Embedded fast planes are invariant under real affine changes of the domain
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic Reeb orbit and $u$ an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then for every $\zeta\in\mathbb{C}$ and every real $\rho>0$, the plane $z\mapsto u(\zeta+\rho z)$ is again an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   It is used to move the base point and adjust the energy normalization of members of a family of planes.
--
--   **Formalization Note** "Fast" is `IsFastPlane H J`, "asymptotic to $P$ at $\infty$" is `IsNondegenerateEnd H · cylInf P 1`, and "embedded" is `IsEmbeddedPlane` (injective with injective derivative).
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Embedded fast finite-energy planes asymptotic to `P` at `∞` stay so under real affine changes of
the domain: if `u` is one, then so is `z ↦ u (ζ + ρ z)` for every `ζ ∈ ℂ` and `ρ > 0`. -/
theorem isFastPlane_comp_add_smul (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (u : ℂ → V 1) (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (ζ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsFastPlane H J (fun z => u (ζ + ρ • z)) ∧
      IsNondegenerateEnd H (fun z => u (ζ + ρ • z)) cylInf P 1 ∧
      IsEmbeddedPlane (fun z => u (ζ + ρ • z)) := by
  sorry

end FiniteEnergyPlane
