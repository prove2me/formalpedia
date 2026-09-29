-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_finrank_of_isClosedImmersion_kernel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_finrank_of_isClosedImmersion_kernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/22c4b68e-d3b4-5fd4-a676-d45262f20be1
-- title:
--   Finite flatness of an ℓ-isogeny from its kernel rank
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $k$ be an algebraically closed field and $\ell$ a prime, and assume $1\in\Lambda$. Let $E,E'$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, i.e. schemes $E.A,E'.A$ with structure morphisms to $\operatorname{Spec} k$, commutative relative group laws on their functors of points, the smooth–proper–connected-fibres bundle, fibres of dimension $2$, and a $\Lambda$-action with its compatibilities. Let $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ be morphisms over $\operatorname{Spec} k$ such that $\varphi$ and $\psi$ are additive on $T$-points for every test morphism $t : T \to \operatorname{Spec} k$, and such that on all such points $\psi\circ\varphi$ and $\varphi\circ\psi$ agree with the $\ell$-fold sum maps of the two group laws. Let $i : K \to E.A$ be a closed immersion which presents the kernel of $\varphi$, in the sense that a point $P$ over $t$ factors through $i$ if and only if $\varphi\circ P$ is the identity section of $E'$ over $t$; assume $i$ followed by $E.f$ is finite and locally of finite presentation, and that its fibre rank at every point of $\operatorname{Spec} k$ is $\ell^2$. Then $\varphi$ is finite, flat, locally of finite presentation and surjective, and $\varphi$ has fibre rank $\ell^2$ at every point $y$ of $E'.A$.
--
--   This converts information about the kernel subscheme of an $\ell$-isogeny of fake elliptic curves into information about the isogeny itself: it is a finite flat surjection of constant degree $\ell^2$. It is used in the extra-level/level-isogeny interface for fake elliptic curves, where kernels of prescribed rank are the given data and degree statements about the isogenies are what is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_finrank_of_isClosedImmersion_kernel.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_finrank_of_isClosedImmersion_kernel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q)
    {K : Scheme.{u}} (i : K ⟶ E.A) (hi : IsClosedImmersion i)
    (hKpt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough i P ↔ mapPt φ hφ P = E'.L.one t)
    (hfin : IsFinite (i ≫ E.f)) (hlfp : LocallyOfFinitePresentation (i ≫ E.f))
    (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), (i ≫ E.f).finrank s = ℓ ^ 2) :
    IsFinite φ ∧ Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ ∧ ∀ y : ↥E'.A, φ.finrank y = ℓ ^ 2 := by sorry
