-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e7047f06-1154-54ba-8d89-cd4e90388bdd
-- title:
--   Descent of an isomorphism of level-ℓ triples to a finitely generated subalgebra
-- statement:
--   Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders, let $N,m,\ell$ be naturals, let $R$ be a noetherian commutative ring and $L$ a commutative $R$-algebra. Let $u,w$ be pairs consisting of a fake elliptic curve over $R$ with $\Lambda$-action and level-$N$ datum together with a full level-$m$ structure, and let $C_u,C_w$ be extra level-$\ell$ structures on them (a closed subscheme $K \to A$, finite flat of finite presentation of rank $\ell^2$, stable under the group law, inversion, the identity, and $\Lambda$, killed by $\ell$, meeting the level-$N$ subscheme only in the identity, with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$). Let $u',w'$ with extra structures $C_{u'},C_{w'}$ be the corresponding data over $L$, and $g_u,g_w$ morphisms over $\operatorname{Spec}$ of the structure map exhibiting $u'$, $w'$ as base changes of $u$, $w$ along $R \to L$ in the sense of `IsPullbackVia` (pullback square, compatibility with the relative group law, with the $\Lambda$-action, and carrying points on the level-$N$ subscheme into it), compatible with the full level sections, and carrying points factoring through $C_{u'}.\mathrm{levK}$, resp. $C_{w'}.\mathrm{levK}$, into $C_u.\mathrm{levK}$, resp. $C_w.\mathrm{levK}$. Assume finally that there is an isomorphism $e : u'.A \cong w'.A$ over $\operatorname{Spec} L$ which is an isomorphism of fake elliptic curves with full level and for which a point factors through $C_{u'}.\mathrm{levK}$ if and only if its image factors through $C_{w'}.\mathrm{levK}$. Then for every finite subset $s \subseteq L$ there are a finitely generated $R$-subalgebra $T \subseteq L$ containing $s$, data $u_T,w_T$ over $T$ with extra level-$\ell$ structures $C_{u_T},C_{w_T}$, and morphisms $g_{u_T}, g_{w_T}$ exhibiting $u_T, w_T$ as base changes of $u,w$ along $R \to T$ in the same sense, compatible with the full level sections, such that a point of $u_T$ (resp. $w_T$) factors through $C_{u_T}.\mathrm{levK}$ (resp. $C_{w_T}.\mathrm{levK}$) if and only if its image under $g_{u_T}$ (resp. $g_{w_T}$) factors through $C_u.\mathrm{levK}$ (resp. $C_w.\mathrm{levK}$) — an equivalence, in contrast to the one-sided hypotheses over $L$ — and such that there is an isomorphism $u_T.A \cong w_T.A$ over $\operatorname{Spec} T$ with the same two properties as $e$.
--
--   This is the level-$\ell$ triple form of the spreading-out step for the quaternionic fine moduli problem: an isomorphism between base changes to $L$ of two triples (fake elliptic curve with full level-$m$ structure and extra level-$\ell$ structure) already exists over some finitely generated $R$-subalgebra of $L$, with the extra level subscheme over $T$ cut out as the exact preimage of the one over $R$. It feeds the statement that such isomorphisms exist over a finitely generated stage uniformly, used in the comparison of the quaternionic moduli problem with its Čerednik–Drinfeld description.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_extraLevel_isPullbackVia_isoTVia_of_isoTVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m ℓ : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L) (Cu' : u'.1.ExtraLevel ℓ) (Cw' : w'.1.ExtraLevel ℓ)
    (gu : u'.1.A ⟶ u.1.A) (gw : w'.1.A ⟶ w.1.A)
    (hgu : FakeEllipticCurve.IsPullbackVia (algebraMap R L) u.1 u'.1 gu)
    (hguP : (u'.2.P).1 ≫ gu = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (u.2.P).1)
    (hguC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ gu)
    (hgw : FakeEllipticCurve.IsPullbackVia (algebraMap R L) w.1 w'.1 gw)
    (hgwP : (w'.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (w.2.P).1)
    (hgwC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' w'.1.f),
      FactorsThrough Cw'.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw)
    (he : ∃ (e : u'.1.A ≅ w'.1.A) (he : e.hom ≫ w'.1.f = u'.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u' w' Cu' Cw' e he)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (uT wT : FakeEllipticCurve.WithFullLevel Λ N m ↥T) (CuT : uT.1.ExtraLevel ℓ) (CwT : wT.1.ExtraLevel ℓ)
        (guT : uT.1.A ⟶ u.1.A) (gwT : wT.1.A ⟶ w.1.A),
        FakeEllipticCurve.IsPullbackVia (algebraMap R ↥T) u.1 uT.1 guT ∧
        (uT.2.P).1 ≫ guT = Spec.map (CommRingCat.ofHom (algebraMap R ↥T)) ≫ (u.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of ↥T)) (P : SchemeHomOver t' uT.1.f),
          FactorsThrough CuT.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ guT) ∧
        FakeEllipticCurve.IsPullbackVia (algebraMap R ↥T) w.1 wT.1 gwT ∧
        (wT.2.P).1 ≫ gwT = Spec.map (CommRingCat.ofHom (algebraMap R ↥T)) ≫ (w.2.P).1 ∧
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of ↥T)) (P : SchemeHomOver t' wT.1.f),
          FactorsThrough CwT.levK P ↔ ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gwT) ∧
        ∃ (e : uT.1.A ≅ wT.1.A) (he : e.hom ≫ wT.1.f = uT.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia uT wT CuT CwT e he := by sorry
