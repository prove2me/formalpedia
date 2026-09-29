-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/bb4c3fb8-7aa2-561a-9e8d-7fac6b78d6b8
-- title:
--   Finite flatness of morphisms of fake elliptic curves with quasi-inverse
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative ring $S$, and let $\mathcal{A}$ and $\mathcal{D}$ be two objects of the project's structure `FakeEllipticCurve Λ N S`: each carries a scheme with a structure morphism to $\operatorname{Spec} S$, a relative group law on its functor of points over $\operatorname{Spec} S$ (functorial multiplication, unit and inverse on points $P$ with $P \circ f = t$), commutativity of that law, the property bundle asserting that the structure morphism is smooth and proper with connected fibres and admits a group law, the requirement that every fibre has topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ compatible with multiplication, addition and the group law together with the trace condition on tangent spaces at geometric points, and further curve data. Let $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ be a morphism over $S$ (that is, $\Phi \circ \mathcal{D}.f = \mathcal{A}.f$) which is a homomorphism on points: for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $P,Q$ of $\mathcal{A}$ over $t$, composing with $\Phi$ carries the product of $P$ and $Q$ to the product of their images. Let $\Psi : \mathcal{D}.A \to \mathcal{A}.A$ be a morphism over $S$ (no homomorphism hypothesis on $\Psi$), and let $n \geq 1$ be such that, on points over any base as above, composing with $\Phi$ and then $\Psi$ equals the $n$-fold iterate $P \mapsto n \cdot P$ of the group law of $\mathcal{A}$, and composing with $\Psi$ and then $\Phi$ equals the corresponding $n$-fold iterate for $\mathcal{D}$. Then $\Phi$ is finite, flat, locally of finite presentation and surjective.
--
--   This is the standard criterion identifying an isogeny: a homomorphism of abelian schemes admitting a quasi-inverse up to multiplication by a positive integer $n$ is finite, flat and surjective, stated here over an arbitrary commutative base for the fake elliptic curves (abelian surfaces with quaternionic multiplication) of the Cerednik–Drinfeld part of the development. It is used by the rigidification results for fake elliptic curves, in particular in the construction of quotients by Atkin–Lehner type automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S]
    (𝒜 𝒟 : FakeEllipticCurve Λ N S)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f)
    (hΦ_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t 𝒜.f),
      mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q))
    (Ψ : 𝒟.A ⟶ 𝒜.A) (hΨ : Ψ ≫ 𝒜.f = 𝒟.f)
    (n : ℕ) (hn : 0 < n)
    (hΨΦ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t 𝒜.f),
      mapPt Ψ hΨ (mapPt Φ hΦ P) = nsmulPt 𝒜.L t n P)
    (hΦΨ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t 𝒟.f),
      mapPt Φ hΦ (mapPt Ψ hΨ Q) = nsmulPt 𝒟.L t n Q) :
    IsFinite Φ ∧ Flat Φ ∧ LocallyOfFinitePresentation Φ ∧ Surjective Φ := by sorry
