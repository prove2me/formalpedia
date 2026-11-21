-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isBounded_preimage_proj_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.isBounded_preimage_proj_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T19:47:57.217196+00:00
-- url     : https://prove2.me/theorems/76a449cb-2c82-4429-92b6-45b4c8c37871
-- title:
--   Preimages of compact sets missing the asymptotic orbit are bounded
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $P=(x,T)$ a periodic Reeb orbit and $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ a map asymptotic to $P$ at $\infty$ in the sense of `IsNondegenerateEnd H u cylInf P 1`. Then for every compact $K\subset\mathbb{R}^{2n+2}$ with $K\cap x(\mathbb{R})=\emptyset$ the set $\{z\in\mathbb{C} : \mathrm{proj}(u(z))\in K\}$ is bounded.
--
--   Role: properness of the $S$-component of a plane asymptotic to $P$, viewed as a map into $S\setminus x(\mathbb{R})$.
--
--   **Formalization Note** No regularity of $u$ is assumed. $K$ need not lie in $S$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 2.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u : ℂ → V n` be asymptotic at `∞` to the periodic Reeb orbit `P`, in the sense of
`IsNondegenerateEnd H u cylInf P 1`. Then for every compact `K ⊆ V n` disjoint from `x(ℝ)` the
set of `z ∈ ℂ` with `proj H (u z) ∈ K` is bounded. -/
theorem isBounded_preimage_proj_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V n)
    (huP : IsNondegenerateEnd H u cylInf P 1) (K : Set (V n)) (hK : IsCompact K)
    (hKP : Disjoint K (Set.range P.x)) :
    Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) := by
  sorry

end FiniteEnergyPlane
