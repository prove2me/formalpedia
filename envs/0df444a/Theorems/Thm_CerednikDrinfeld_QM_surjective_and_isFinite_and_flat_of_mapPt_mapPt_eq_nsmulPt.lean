-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
-- name    : CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0ad5046a-f197-5852-8572-89855efe9e62
-- title:
--   Isogeny criterion: surjective, finite and flat
-- statement:
--   Let $k$ be an algebraically closed field. Let $f \colon A \to \operatorname{Spec} k$ and $f' \colon A' \to \operatorname{Spec} k$ be schemes over $k$, each carrying a relative group law ($L$, resp. $L'$): a group structure on the set $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over $k$, for every $k$-scheme $t \colon T \to \operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$; both are assumed commutative ($hc$, $hc'$). Both $f$ and $f'$ are assumed to satisfy `AbelianSchemePropertyBundle`, i.e. to be smooth and proper, to have connected fibres (the preimage under the underlying map of each point of $\operatorname{Spec} k$ is connected), and to admit some relative group law. Let $\varphi \colon A \to A'$ satisfy $\varphi$ followed by $f'$ equals $f$, and assume that the induced map $P \mapsto P$ followed by $\varphi$ on $T$-valued points is a homomorphism from $L$ to $L'$ for every $k$-scheme $T$. Let $\psi \colon A' \to A$ be a morphism over $k$ and $n > 0$ a natural number such that, on $T$-valued points for every $k$-scheme $T$, composing with $\varphi$ and then with $\psi$ gives the $n$-fold $L$-power (defined recursively by $0 \mapsto$ unit, $m+1 \mapsto$ the $m$-fold power multiplied by the point), and composing with $\psi$ and then with $\varphi$ gives the $n$-fold $L'$-power. Then $\varphi$ is surjective, finite and flat as a morphism of schemes. No homomorphism hypothesis is imposed on $\psi$.
--
--   This is the classical statement that an isogeny of abelian varieties over an algebraically closed field — presented here in the form of a homomorphism admitting a two-sided quasi-inverse up to multiplication by a positive integer $n$, with no restriction on the characteristic — is a finite, faithfully flat morphism. It is used in the Čerednik–Drinfeld part of the development, where it feeds the results on level isogenies and on degrees of endomorphisms of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
    (hc' : L'.IsCommutative) (hA' : AbelianSchemePropertyBundle k f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ : A' ⟶ A) (hψ : ψ ≫ f = f') (n : ℕ) (hn : 0 < n)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt L t n P)
    (hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f'),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt L' t n Q) :
    Surjective φ ∧ IsFinite φ ∧ Flat φ := by sorry
