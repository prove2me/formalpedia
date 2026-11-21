-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ne_proj_eq_of_proj_mem_range
-- name    : FiniteEnergyPlane.exists_ne_proj_eq_of_proj_mem_range
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T00:36:15.112098+00:00
-- url     : https://prove2.me/theorems/18b9db01-971a-4954-b1e0-47257f26ab59
-- title:
--   A fast plane whose S-component meets its asymptotic orbit has a double point in S
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde u:\mathbb{C}\to\mathbb{R}^4$ a fast finite-energy plane asymptotic to the periodic Reeb orbit $P=(x,T)$ at $\infty$, with $S$-component $u=\mathrm{pr}\circ\tilde u$. If $u(z_0)\in x(\mathbb{R})$ for some $z_0\in\mathbb{C}$, then $u$ has a double point: there are $z\neq w$ with $u(z)=u(w)$.
--
--   Role: a plane whose $S$-component meets the asymptotic orbit cannot have an injective $S$-component. Together with injectivity results for embedded planes, this excludes intersections of $\tilde u(\mathbb{C})$ with the cylinder $\mathbb{R}\times x(\mathbb{R})$.
--
--   **Formalization Note** "Fast" is `IsFastPlane`, and the end at $\infty$ is `IsNondegenerateEnd H u cylInf P 1`. The hypothesis is `proj H (u z₀) ∈ Set.range P.x`. Neither embeddedness nor any index condition on $P$ is assumed.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.24

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A fast plane whose `S`-component meets its asymptotic orbit has a double point in `S`. Let
`u` be a fast finite-energy plane asymptotic to `P` at `∞` with `proj H (u z₀) ∈ x(ℝ)` for some
`z₀`. Then there are `z ≠ w` with `proj H (u z) = proj H (u w)`. -/
theorem exists_ne_proj_eq_of_proj_mem_range (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (z₀ : ℂ)
    (hz₀ : proj H (u z₀) ∈ Set.range P.x) :
    ∃ z w : ℂ, z ≠ w ∧ proj H (u z) = proj H (u w) := by
  sorry

end FiniteEnergyPlane
