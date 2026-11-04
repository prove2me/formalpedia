-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isProperEmbedding_proj_of_isFastPlane
-- name    : FiniteEnergyPlane.isProperEmbedding_proj_of_isFastPlane
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:09:33.009328+00:00
-- url     : https://prove2.me/theorems/18bda440-d759-4dbc-a024-96ca65f0f640
-- title:
--   Fast planes missing their asymptotic orbit project to proper embeddings
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $u$ a fast finite-energy plane asymptotic to $P$ at $\infty$ whose $S$-component $\mathrm{proj}\circ u$ does not meet $x(\mathbb{R})$. Then $\mathrm{proj}\circ u:\mathbb{C}\to S\setminus x(\mathbb{R})$ is a proper embedding.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. "Proper embedding of $\mathbb{C}$ into $S\setminus x(\mathbb{R})$" is stated as: $\mathrm{proj}\circ u$ is injective, its derivative is injective at every point, and $(\mathrm{proj}\circ u)^{-1}(K)$ is bounded for every compact $K\subset\mathbb{R}^4$ disjoint from $x(\mathbb{R})$. The plane $u$ is not assumed to be embedded.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, doi:10.1007/BF01895669, Theorem 2.3

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 6.22. Let `u` be a fast finite-energy plane asymptotic to
`P` at `∞` whose `S`-component `proj H ∘ u` does not meet `x(ℝ)`. Then `proj H ∘ u` is a proper
embedding of `ℂ` into `S \ x(ℝ)`: it is injective, its derivative is injective at every point, and
the preimage of every compact set disjoint from `x(ℝ)` is bounded. -/
theorem isProperEmbedding_proj_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hmiss : ∀ z, proj H (u z) ∉ Set.range P.x) :
    Function.Injective (proj H ∘ u) ∧
      (∀ z, Function.Injective (fderiv ℝ (proj H ∘ u) z)) ∧
      ∀ K : Set (V 1), IsCompact K → Disjoint K (Set.range P.x) →
        Bornology.IsBounded ((proj H ∘ u) ⁻¹' K) := by
  sorry

end FiniteEnergyPlane
