-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_of_proj_eq_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_eq_of_proj_eq_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T19:48:07.07161+00:00
-- url     : https://prove2.me/theorems/a7f0aa53-d2b4-4daa-93e7-a1fc662b74ea
-- title:
--   Far points of a fast plane are the only preimages of their S-values
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $u$ a fast finite-energy plane asymptotic to $P$ at $\infty$ whose $S$-component $\mathrm{proj}\circ u$ does not meet $x(\mathbb{R})$. Then there is $R$ such that for every $z\in\mathbb{C}$ with $|z|\ge R$ and every $z'\in\mathbb{C}$,
--   $$\mathrm{proj}(u(z))=\mathrm{proj}(u(z'))\ \Longrightarrow\ z=z'.$$
--
--   Role: near the puncture the $S$-component of such a plane takes each of its values exactly once on all of $\mathbb{C}$ (Hryniewicz 2012, (100)); this is the input about the end needed for Lemma 6.22.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1`; "fast" is `IsFastPlane` (its prime orbit is existentially quantified and not assumed equal to $P$; $P$ itself is not assumed prime). $\mathrm{proj}$ is `proj H`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 2.3

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), (100), for fast planes. Let `u` be a fast finite-energy plane
asymptotic to `P` at `∞` whose `S`-component `proj H ∘ u` does not meet `x(ℝ)`. Then there is
`R` such that every point `z` with `‖z‖ ≥ R` is the only point of `ℂ` at which `proj H ∘ u` takes
the value `proj H (u z)`. -/
theorem exists_eq_of_proj_eq_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    ∃ R : ℝ, ∀ z z' : ℂ, R ≤ ‖z‖ → proj H (u z) = proj H (u z') → z = z' := by
  sorry

end FiniteEnergyPlane
