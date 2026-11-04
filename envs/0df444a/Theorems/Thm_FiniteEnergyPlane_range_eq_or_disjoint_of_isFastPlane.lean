-- Prove2me | Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isFastPlane
-- name    : FiniteEnergyPlane.range_eq_or_disjoint_of_isFastPlane
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:09:56.817179+00:00
-- url     : https://prove2.me/theorems/f4dbb4c7-1b06-4098-b08d-d7eb6ce017e6
-- title:
--   Embedded fast planes over the same orbit have equal or disjoint images
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and let $u$ and $v$ be embedded fast finite-energy planes asymptotic to $P$ at $\infty$ whose $S$-components do not meet $x(\mathbb{R})$. Then the images $\mathrm{proj}(u(\mathbb{C}))$ and $\mathrm{proj}(v(\mathbb{C}))$ are equal or disjoint.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. Hryniewicz also assumes $\beta_{\tilde u}=\beta_{\tilde v}$, where $\beta_{\tilde u}$ is the class of trivializations of $\xi$ along $P$ that extend over the capping disk $u$. On a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so $\beta_{\tilde u}=\beta_{\tilde v}$ holds for any two planes asymptotic to $P$ and is not restated. No index hypothesis is made.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), 270–328, doi:10.1007/BF01895669, Theorem 4.11

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 6.23; Hofer–Wysocki–Zehnder (GAFA 1995), Theorem 4.11.
Let `u` and `v` be embedded fast finite-energy planes asymptotic to the same orbit `P` at `∞`,
whose `S`-components do not meet `x(ℝ)`. Then the images of `proj H ∘ u` and `proj H ∘ v` are
equal or disjoint. -/
theorem range_eq_or_disjoint_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    Set.range (proj H ∘ u) = Set.range (proj H ∘ v) ∨
      Disjoint (Set.range (proj H ∘ u)) (Set.range (proj H ∘ v)) := by
  sorry

end FiniteEnergyPlane
