-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/9888bae4-8604-59bd-87a6-4c33eb68604b
-- title:
--   Two-sided n-isogenies of fake elliptic curves are finite and flat
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a field $L$ and a valuation subring $O$ of $L$. Let $\mathcal{A}$ and $\mathcal{D}$ be fake elliptic curves of type `FakeEllipticCurve Λ N ↥O`: each consists of a scheme with a structure morphism to $\operatorname{Spec} O$, a commutative relative group law on its functor of points over $O$, the property bundle asserting that the structure morphism is smooth and proper with connected fibres and admits a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative on points and satisfies the trace condition relating $m+\bar m$ to the trace on tangent spaces, together with the remaining curve data. Let $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ be a morphism over $\operatorname{Spec} O$ which, for every scheme $T$ and every $t : T \to \operatorname{Spec} O$, carries the group law product of two $T$-points of $\mathcal{A}$ over $t$ (morphisms $T \to \mathcal{A}.A$ composing with the structure morphism to $t$) to the product of their images under post-composition with $\Phi$. Let $\Psi : \mathcal{D}.A \to \mathcal{A}.A$ be a morphism over $\operatorname{Spec} O$, not assumed to be a homomorphism, and let $n \ge 1$ be such that both composites induce $n$-fold addition on points: post-composition with $\Phi$ followed by $\Psi$ sends every $T$-point $P$ of $\mathcal{A}$ to $nP$ for the group law of $\mathcal{A}$, and symmetrically for $\Psi$ followed by $\Phi$ on $T$-points of $\mathcal{D}$, where $nP$ is defined recursively from the unit section. Then $\Phi$ is finite, flat, locally of finite presentation and surjective.
--
--   This is the basic finiteness statement for an isogeny between fake elliptic curves (abelian surfaces with quaternionic multiplication) over a valuation ring: a morphism admitting a two-sided quasi-inverse up to multiplication by $n$ on points is finite flat surjective. It is used in the Čerednik–Drinfeld part of the argument, in the analysis of extra level structures and of kernels of level isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_mapPt_mapPt_eq_nsmulPt_valuationSubring
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {L : Type u} [Field L] (O : ValuationSubring L)
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f)
    (hΦ_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q))
    (Ψ : 𝒟.A ⟶ 𝒜.A) (hΨ : Ψ ≫ 𝒜.f = 𝒟.f)
    (n : ℕ) (hn : 0 < n)
    (hΨΦ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      mapPt Ψ hΨ (mapPt Φ hΦ P) = nsmulPt 𝒜.L t n P)
    (hΦΨ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (Q : SchemeHomOver t 𝒟.f),
      mapPt Φ hΦ (mapPt Ψ hΨ Q) = nsmulPt 𝒟.L t n Q) :
    IsFinite Φ ∧ Flat Φ ∧ LocallyOfFinitePresentation Φ ∧ Surjective Φ := by sorry
