-- Prove2me | Theorems.Thm_FiniteEnergyPlane_range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet
-- name    : FiniteEnergyPlane.range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:35:17.017859+00:00
-- url     : https://prove2.me/theorems/e37c06ce-b61a-4b9b-86fb-1a9fd7c5cec5
-- title:
--   Leaves that meet coincide
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$. If $u\in\Lambda(K,P)$ and $v\in\Lambda(K',P)$ (with possibly different energy constants) and $\mathrm{proj}(u(z))=\mathrm{proj}(v(z'))$ for some $z,z'$, then $\mathrm{proj}(u(\mathbb{C}))=\mathrm{proj}(v(\mathbb{C}))$.
--
--   Reusable form of the alternative that leaves are equal or disjoint.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Two planes of sets `Λ` whose projections share a point have the same projected image. -/
theorem range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ γ' : ℝ) (K K' : Set (V 1)) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P K γ) (hv : v ∈ embeddedFastPlaneSet H J P K' γ')
    (z z' : ℂ) (h : proj H (u z) = proj H (v z')) :
    Set.range (fun z => proj H (u z)) = Set.range (fun z => proj H (v z)) := by
  sorry

end FiniteEnergyPlane
