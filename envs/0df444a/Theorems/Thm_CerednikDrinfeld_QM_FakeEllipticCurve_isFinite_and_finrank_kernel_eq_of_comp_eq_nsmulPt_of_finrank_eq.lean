-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2926d6f7-6ef5-56ad-bf7b-e3be32a5a0b9
-- title:
--   Rank ℓ² for the kernel of the partner isogeny
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $k$ be an algebraically closed field and $\ell$ a natural number assumed prime. Let $E$ and $E'$ be fake elliptic curves of type $(\Lambda,N)$ over $k$, each consisting of a scheme with a structure morphism to $\operatorname{Spec} k$, a commutative relative group law on its functor of points, the abelian-scheme property bundle (smooth, proper, connected fibres, group law present), two-dimensional fibres and a $\Lambda$-action with the stated compatibilities. Let $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ be morphisms over $\operatorname{Spec} k$, i.e. $\varphi$ followed by $E'.f$ is $E.f$ and $\psi$ followed by $E.f$ is $E'.f$. Assume both are homomorphisms for the group laws: for every scheme $T$, every $t : T \to \operatorname{Spec} k$ and all $T$-points $P,Q$ over the relevant structure morphism, composing with $\varphi$ (respectively $\psi$) carries the product of $P$ and $Q$ to the product of their images. Assume further that composing a point with $\varphi$ and then with $\psi$ yields the $\ell$-fold sum $P + \cdots + P$ formed by the iterated group law from the identity point, for all $T$, $t$ and $P$; and that $\varphi$ is finite, flat, locally of finite presentation, surjective, with $\varphi.\mathrm{finrank}\, y = \ell^2$ at every point $y$ of $E'.A$. The conclusion concerns the fibre product of $\psi$ with the identity section $\operatorname{Spec} k \to E.A$ of $E$'s group law: the first projection of this pullback followed by $E'.f$ is finite, is locally of finite presentation, and has rank $\ell^2$ at every point $s$ of $\operatorname{Spec} k$.
--
--   This is the multiplicativity of degrees in the factorisation $[\ell] = \psi\varphi$ for a fake elliptic curve, an abelian surface, where $\ker[\ell]$ has rank $\ell^4$ and $\ker\varphi$ rank $\ell^2$, so the scheme-theoretic kernel of the partner $\psi$ again has rank $\ell^2$. It supplies the rank datum used when an $\ell$-isogeny of fake elliptic curves is converted into extra level structure, and hence in the construction of level isogenies and their flips.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_finrank_kernel_eq_of_comp_eq_nsmulPt_of_finrank_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    (E E' : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P)
    (hφfin : IsFinite φ) (hφflat : Flat φ) (hφlfp : LocallyOfFinitePresentation φ) (hφsurj : Surjective φ)
    (hφrank : ∀ y : ↥E'.A, φ.finrank y = ℓ ^ 2) :
    IsFinite ((pullback.fst ψ (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E'.f)) ∧
    LocallyOfFinitePresentation ((pullback.fst ψ (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E'.f)) ∧
    ∀ s : ↥(Spec (CommRingCat.of k)), ((pullback.fst ψ (E.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E'.f)).finrank s = ℓ ^ 2 := by sorry
