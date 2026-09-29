-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_forall_iso_of_iso_hom_act
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_forall_iso_of_iso_hom_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/8386f6ba-8064-54ef-829a-8749990b1659
-- title:
--   Finitely many level-N structures on a fixed fake elliptic curve
-- statement:
--   Fix rationals $a,b$, an additive subgroup $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ (an $\mathbb{Z}$-submodule of the quaternion algebra), natural numbers $N, N_1$, an algebraically closed field $k$ with $N \neq 0$ in $k$, and a `FakeEllipticCurve Λ N₁ k` $E_1$ — that is, a scheme $A$ over $\operatorname{Spec} k$ carrying a commutative relative group law on its functor of points, smooth, proper, with connected fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms over the base which are additive both in the point and in the element of $\Lambda$, are unital and anti‑multiplicative, satisfy the trace condition on tangent spaces, and a level datum $C \to A$. The assertion is that there exist $m \in \mathbb{N}$ and a family $T : \mathrm{Fin}\,m \to$ `FakeEllipticCurve Λ N k` with the following property: whenever $E$ is a fake elliptic curve of level $N$ over $k$ and $e : E.A \cong E_1.A$ is an isomorphism of schemes with $e.\mathrm{hom}$ followed by $E_1.f$ equal to $E.f$, such that $e.\mathrm{hom}$ carries the group law of $E$ to that of $E_1$ on $T'$-points for every base $t : T' \to \operatorname{Spec} k$, and such that $E.\mathrm{act}\,x$ followed by $e.\mathrm{hom}$ equals $e.\mathrm{hom}$ followed by $E_1.\mathrm{act}\,x$ for every $x \in \Lambda$, then $E$ is isomorphic to some $T\,i$ in the sense of `FakeEllipticCurve.Iso`: there is an isomorphism over $\operatorname{Spec} k$ compatible with the group laws and with the $\Lambda$-actions, and under which a point factors through the level map of $E$ if and only if its image factors through that of $T\,i$.
--
--   This is the finiteness of the set of level-$N$ structures, up to isomorphism, on a fixed quaternionic ("fake elliptic") abelian surface over an algebraically closed field in which $N$ is invertible, phrased as the existence of a finite list of representatives. It feeds the counting of fake elliptic curves with prescribed underlying abelian surface with $\Lambda$-action, and is used in `exists_fin_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow_of_level_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_forall_iso_of_iso_hom_act.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld
open CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_forall_iso_of_iso_hom_act
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N N₁ : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0) (E₁ : FakeEllipticCurve Λ N₁ k) :
    ∃ (m : ℕ) (T : Fin m → FakeEllipticCurve Λ N k),
      ∀ (E : FakeEllipticCurve Λ N k) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) →
        ∃ i : Fin m, FakeEllipticCurve.Iso E (T i) := by sorry
