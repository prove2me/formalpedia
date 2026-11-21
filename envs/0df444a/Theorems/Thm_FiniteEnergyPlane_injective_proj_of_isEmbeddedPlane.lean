-- Prove2me | Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
-- name    : FiniteEnergyPlane.injective_proj_of_isEmbeddedPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T00:25:50.317443+00:00
-- url     : https://prove2.me/theorems/dc7caffa-b439-4d02-9977-10ee6f230dd5
-- title:
--   The S-component of an embedded fast plane is injective
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde u:\mathbb{C}\to\mathbb{R}^4$ an embedded fast finite-energy plane asymptotic to the periodic Reeb orbit $P$ at $\infty$. Write $u=\mathrm{pr}\circ\tilde u:\mathbb{C}\to S$ for its $S$-component. Then $u$ is injective: no two distinct points of $\tilde u(\mathbb{C})$ lie on the same ray from the origin.
--
--   Role: equivalently, the plane $\tilde u$ meets none of its translates $c\cdot\tilde u$, $c\neq0$, in the $\mathbb{R}$-direction of the symplectization. This is the embeddedness of the projected plane used for Hryniewicz's Lemmas 6.24 and 6.25.
--
--   **Formalization Note** "Embedded" is `IsEmbeddedPlane` (injective with injective derivative everywhere), "fast" is `IsFastPlane`, and the end at $\infty$ is `IsNondegenerateEnd H u cylInf P 1`. No index condition on $P$ is assumed, and $u(\mathbb{C})$ is not assumed to avoid $x(\mathbb{R})$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.24; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, Progr. Nonlinear Differential Equations Appl. 35 (1999), Lemma 8.1

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The `S`-component of an embedded fast plane is injective. Let `u` be an embedded fast
finite-energy plane asymptotic to `P` at `∞`. Then `z ↦ proj H (u z)` is injective, i.e. no two
distinct points of `u(ℂ)` lie on the same ray from the origin. -/
theorem injective_proj_of_isEmbeddedPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u) :
    Function.Injective (fun z => proj H (u z)) := by
  sorry

end FiniteEnergyPlane
