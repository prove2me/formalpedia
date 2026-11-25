-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_embedded_fastPlane_of_spanningDisk
-- name    : FiniteEnergyPlane.exists_embedded_fastPlane_of_spanningDisk
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:40:37.742848+00:00
-- url     : https://prove2.me/theorems/7687cacf-26e5-4465-ad2f-a69e47f29e4e
-- title:
--   Existence of an embedded fast finite-energy plane from a special spanning disk
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$. Let $P=(x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$: $e$ embeds a disk slightly larger than the closed unit disk into $S$, with exactly one tangency to $\xi$, which is positive and nicely elliptic; it maps the unit circle onto $x(\mathbb{R})$ in the direction of $R$; all its characteristic leaves issue from the singular point and reach the boundary; $R$ is not tangent to it near the boundary; and it contains no periodic Reeb orbit other than $x(\mathbb{R})$. Let
--   $$\int_{\mathring D}\max\big(\omega_0(\partial_se,\partial_te),0\big)\,ds\,dt<C,$$
--   where $\mathring D$ is the open unit disk, and suppose every periodic Reeb orbit of period at most $C$ is nondegenerate with $\mu_{CZ}\ge3$. Then there are a smooth $d\lambda_0$-compatible complex structure $J$ on $\xi$ and an embedded fast finite-energy $\tilde J$-holomorphic plane asymptotic to $P$ at $\infty$.
--
--   Such a plane is the remaining hypothesis in the open book theorem `exists_fastPlane_open_book`, and no dynamical convexity beyond period $C$ is assumed.
--
--   **Formalization Note** The special spanning disk is `IsSpecialSpanningDisk`, and the integral is `diskArea e`. Periods are those of `ReebOrbit H`, not necessarily minimal, so multiple covers count. $\mu_{CZ}\ge3$ is `IsCZAtLeast 3`, measured in the global frame of $\xi$. $T\le C$ is not a hypothesis. The source starts from an unknotted orbit of self-linking number $-1$ for which such a disk is constructed, and lets the contact form vary in a sequence; here the disk is given and the level is fixed. The leaf condition is part of the assumptions of Hofer–Wysocki–Zehnder (1999, Section 11). The source fixes the homotopy class of the disks, see `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Theorem 3.4; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, § 5.3

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Theorem 3.4, and Hryniewicz (2012), § 5.3, for a fixed strictly star-shaped level
`S = H⁻¹(1) ⊂ ℝ⁴` and a given special spanning disk. Let `P` be a prime periodic Reeb orbit with a special spanning
disk `e` (`IsSpecialSpanningDisk`) whose positive `dλ₀`-area is less than `C`, and suppose every periodic
Reeb orbit of period at most `C` is nondegenerate with Conley–Zehnder index at least `3`. Then for some
compatible complex structure `J` on `ξ` there is an embedded fast finite-energy `J̃`-holomorphic plane
asymptotic to `P` at `∞`. -/
theorem exists_embedded_fastPlane_of_spanningDisk (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (C : ℝ) (hC : diskArea e < ENNReal.ofReal C)
    (hQ : ∀ Q : ReebOrbit H, Q.T ≤ C → Q.IsNondegenerate ∧ Q.IsCZAtLeast 3) :
    ∃ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J ∧ ∃ u₀ : ℂ → V 1,
      IsFastPlane H J u₀ ∧ IsNondegenerateEnd H u₀ cylInf P 1 ∧ IsEmbeddedPlane u₀ := by
  sorry

end FiniteEnergyPlane
