-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_isolated_of_isBounded_of_isClosed
-- name    : FiniteEnergyPlane.forall_isolated_of_isBounded_of_isClosed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:11:29.587606+00:00
-- url     : https://prove2.me/theorems/36335a3d-2420-4970-9fee-fdd9760635fe
-- title:
--   Bounded closed intersection sets of immersed planes are discrete
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and let $u,v:\mathbb{C}\to\mathbb{R}^4$ be finite-energy $\tilde J$-holomorphic planes that are immersions ($du(z)$ and $dv(w)$ injective for all $z,w$). Let $O\subset\mathbb{C}\times\mathbb{C}$ be open and suppose the set
--   $$A=\{(z,w)\in O : u(z)=v(w)\}$$
--   is closed and bounded. Then every $(z_0,w_0)\in A$ is isolated: there is $\varepsilon>0$ such that $z\in B_\varepsilon(z_0)$, $w\in B_\varepsilon(w_0)$ and $u(z)=v(w)$ imply $(z,w)=(z_0,w_0)$.
--
--   Role: discreteness of the intersection set of two immersed planes (or of one plane with itself, with $O$ the complement of the diagonal) as soon as that set is compact; used for intersection arguments with translates in the symplectization.
--
--   **Formalization Note** "Finite-energy $\tilde J$-holomorphic plane" is `IsFiniteEnergyCurve H J Set.univ`. $u=v$ is allowed. Closedness is required of $A$ itself, not only of its closure in $O$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 4.11

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Intersections of two immersed finite-energy `J̃`-holomorphic planes `u, v : ℂ → ℝ⁴` inside an
open set `O ⊆ ℂ × ℂ`: if the set of pairs `(z, w) ∈ O` with `u z = v w` is closed and bounded,
then each such pair is isolated, i.e. it is the only pair with `u z = v w` in some product of
balls around it. -/
theorem forall_isolated_of_isBounded_of_isClosed (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hv : IsFiniteEnergyCurve H J Set.univ v)
    (hui : ∀ z, Function.Injective (fderiv ℝ u z)) (hvi : ∀ w, Function.Injective (fderiv ℝ v w))
    (O : Set (ℂ × ℂ)) (hO : IsOpen O)
    (hcl : IsClosed {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (hbd : Bornology.IsBounded {p : ℂ × ℂ | p ∈ O ∧ u p.1 = v p.2})
    (p : ℂ × ℂ) (hp : p ∈ O) (hpe : u p.1 = v p.2) :
    ∃ ε > 0, ∀ z ∈ ball p.1 ε, ∀ w ∈ ball p.2 ε, u z = v w → z = p.1 ∧ w = p.2 := by
  sorry

end FiniteEnergyPlane
