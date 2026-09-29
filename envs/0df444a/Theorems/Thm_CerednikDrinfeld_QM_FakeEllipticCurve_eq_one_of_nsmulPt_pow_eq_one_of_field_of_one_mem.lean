-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7155c3a0-1464-580c-9a38-08a714f8b9b8
-- title:
--   Field-valued q-power torsion of a fake elliptic curve is trivial
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a prime $q$. Let $\mathrm{coord}\colon \Lambda \to \mathrm{Zp2}\,q \times \mathrm{Zp2}\,q$, with $\mathrm{Zp2}\,q = \mathrm{WittVector}\,q\,(\mathrm{GaloisField}\,q\,2)$, satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, has $q$-adically dense image in each coordinate, satisfies the twisted multiplication rule $\mathrm{coord}(mm') = (c_1c'_1 + q\,c_2\varphi(c'_2),\, c_1c'_2 + c_2\varphi(c'_1))$ with $\varphi$ the Witt vector Frobenius, and the trace rule: $m + \bar m = n \in \mathbb{Z}$ forces $c_1 + \varphi(c_1) = n$. Assume $1 \in \Lambda$. Let $B$ be a commutative ring in which the image of $q$ is nilpotent, $E$ a fake elliptic curve over $B$ of type $(\Lambda,N)$, $X$ a two-dimensional formal $\mathcal{O}_D$-module over $B$ (a formal group $X.F$ with $\mathrm{Zp2}\,q$-action and uniformiser series), and $\theta$ a system of formal coordinates, assigning to each $B$-algebra $B'$ and each pair of elements of $B'$ a point of $E$ over $\mathrm{Spec}\,B'$, such that `IsFormalModuleVia` holds: $\theta$ presents the infinitesimal points of the group law $E.L$ via $X.F$, and the action of each $m \in \Lambda$ is computed in these coordinates by the series $\mathrm{addVia}\,X.F\,(X.\mathrm{act}\,c_1)\,((X.\mathrm{act}\,c_2)\circ X.\varpi)$. Then for every field $\kappa$ that is a $B$-algebra, every $m \in \mathbb{N}$, and every point $P$ of $E$ over $\mathrm{Spec}\,\kappa$ (a morphism $\mathrm{Spec}\,\kappa \to E.A$ lying over the structural map), $q^m P = e$ in the group law $E.L$ implies $P = e$.
--
--   This is the absence of non-trivial $q$-power torsion among field-valued points of a fake elliptic curve at a prime $q$ where the quaternion algebra ramifies, the $\mathcal{O}_D$-module structure on the formal group forcing the formal part to absorb all $q$-power torsion. It is the version carrying the hypothesis $1 \in \Lambda$, needed so that the unit of $\Lambda$ acts as the identity, and it is used to show that the $q$-power torsion of $E$ is infinitesimal, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNilpotent_isInfinitesimal_of_nsmulPt_pow_eq_one_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isNilpotent_isInfinitesimal_of_nsmulPt_pow_eq_one_of_one_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_nsmulPt_pow_eq_one_of_field_of_one_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (κ : Type) [Field κ] [Algebra B κ] (m : ℕ)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) κ) E.f)
    (hP : nsmulPt E.L (Scheme.specOver (𝒪 := B) κ) (q ^ m) P = E.L.one (Scheme.specOver (𝒪 := B) κ)) :
    P = E.L.one (Scheme.specOver (𝒪 := B) κ) := by sorry
