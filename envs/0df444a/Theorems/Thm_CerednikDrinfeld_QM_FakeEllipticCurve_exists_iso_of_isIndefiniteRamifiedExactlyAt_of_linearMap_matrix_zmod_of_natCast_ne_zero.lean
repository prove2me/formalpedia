-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/1c46885f-c82c-5f8e-8ca0-d79c633cff2c
-- title:
--   Relevelling a fake elliptic curve over an algebraically closed field
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and primes $q,q'$ such that $\mathrm{IsIndefiniteRamifiedExactlyAt}$ holds for $\mathbb{H}[\mathbb{Q},a,b]$: either $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such submodules. Let $M$ and $N$ be natural numbers with $N\neq 0$, and let $\varphi:\Lambda\to M_2(\mathbb{Z}/N)$ be a $\mathbb{Z}$-linear map sending $1$ to $1$, satisfying $\varphi(xy)=\varphi(x)\varphi(y)$ whenever $xy\in\Lambda$, surjective, and with $\varphi(x)=0$ if and only if $x\in N\Lambda$. Let $k$ be an algebraically closed field with $N\neq 0$ in $k$, and let $E$ be a fake elliptic curve over $k$ for $\Lambda$ of level $M$. Then there exist a fake elliptic curve $E'$ over $k$ for $\Lambda$ of level $N$ and morphisms $u:E'.A\to E.A$, $u':E.A\to E'.A$ with $u$ a morphism over $\mathrm{Spec}\,k$ (that is, $u$ followed by $E.f$ equals $E'.f$), such that $u,u'$ are mutually inverse isomorphisms, $u$ carries the group law of $E'$ to that of $E$ on points over any base $T\to\mathrm{Spec}\,k$, and $E'.\mathrm{act}(x)$ followed by $u$ equals $u$ followed by $E.\mathrm{act}(x)$ for every $x\in\Lambda$.
--
--   The statement records that the level of a fake elliptic curve over an algebraically closed field in which $N$ is invertible may be changed from $M$ to $N$ without altering the underlying $\Lambda$-abelian surface: the new object is isomorphic to the old one compatibly with the group laws and the $\Lambda$-actions, so that any structure carried by $E$ transports to $E'$ by conjugation with $u$. It is used in the construction of fake elliptic curves equipped with formal module and endomorphism data, in the Čerednik–Drinfeld part of the treatment of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isIndefiniteRamifiedExactlyAt_of_linearMap_matrix_zmod_of_natCast_ne_zero
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {M : ℕ} (N : ℕ) [NeZero N]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφ_surj : Function.Surjective φ)
    (hφ_ker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (k : Type) [Field k] [IsAlgClosed k] (hN : (N : k) ≠ 0) (E : FakeEllipticCurve Λ M k) :
    ∃ (E' : FakeEllipticCurve Λ N k) (u : E'.A ⟶ E.A) (u' : E.A ⟶ E'.A) (hu : u ≫ E.f = E'.f),
      u ≫ u' = 𝟙 E'.A ∧ u' ≫ u = 𝟙 E.A ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
        mapPt u hu (E'.L.mul t P Q) = E.L.mul t (mapPt u hu P) (mapPt u hu Q)) ∧
      (∀ x : ↥Λ, E'.act x ≫ u = u ≫ E.act x) := by sorry
