-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_forall_isoTVia_of_isoTVia_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_forall_isoTVia_of_isoTVia_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/952ca435-65fa-58fd-b064-fd1808032610
-- title:
--   Spreading out an isomorphism of levelled fake elliptic curves
-- statement:
--   Fix rationals $a,b$ and a submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Z}$ which is a maximal order (an order whose only order containing it is itself), natural numbers $N, m, \ell$, a noetherian commutative ring $R$ and a commutative $R$-algebra $L$. Let $u, w$ be fake elliptic curves for $\Lambda$ with level $N$ over $R$ together with full level-$m$ structures, equipped with extra level-$\ell$ data $C_u, C_w$ (closed immersions $K \to A$ that are finite, flat, of finite presentation and of fibre rank $\ell^2$ over the base, stable under the $\Lambda$-action, killed by $\ell$, and disjoint from the level-$N$ subscheme), and let $u', w'$ with $C_{u'}, C_{w'}$ be such data over $L$. Let $g_u : u'.A \to u.A$ and $g_w : w'.A \to w.A$ exhibit $u', w'$ as base changes of $u, w$ along $R \to L$ in the sense that each square over $\operatorname{Spec}$ of the structure map is cartesian, the group laws and the $\Lambda$-actions are respected, and level-$N$ points are carried to level-$N$ points; assume in addition that $g_u, g_w$ carry the full level-$m$ sections of $u', w'$ to those of $u, w$ over $\operatorname{Spec}$ of the structure map, and that every point factoring through $C_{u'}.\mathrm{levK}$ (respectively $C_{w'}.\mathrm{levK}$) has its image under $g_u$ (respectively $g_w$) factoring through $C_u.\mathrm{levK}$ (respectively $C_w.\mathrm{levK}$). Assume there is an isomorphism $e : u'.A \cong w'.A$ over $\operatorname{Spec} L$ which is an isomorphism of the whole package: compatible with the group laws and the $\Lambda$-actions, matching the level-$N$ subschemes in both directions, carrying the full level-$m$ section of $u'$ to that of $w'$, and matching factorisation through $C_{u'}.\mathrm{levK}$ with factorisation through $C_{w'}.\mathrm{levK}$. Then for every finite subset $s \subseteq L$ there is an $R$-subalgebra $T \subseteq L$, finitely generated as an $R$-algebra, containing $s$, with the following property: for every commutative ring $B$ and ring homomorphisms $\varphi : T \to B$, $\chi : R \to B$ with $\varphi \circ (R \to T) = \chi$, and for all data $u_B, w_B$ over $B$ with full level-$m$ and extra level-$\ell$ structures $C_{u_B}, C_{w_B}$ and morphisms $g_{u_B} : u_B.A \to u.A$, $g_{w_B} : w_B.A \to w.A$ exhibiting $u_B, w_B$ as base changes of $u, w$ along $\chi$ in exactly the same threefold sense (cartesian square with group law, action and level-$N$ compatibility; full level-$m$ sections matched; extra level points sent into $C_u.K$, $C_w.K$), there exists an isomorphism $u_B.A \cong w_B.A$ over $\operatorname{Spec} B$ which is such an isomorphism of the full packages for $u_B, w_B, C_{u_B}, C_{w_B}$.
--
--   This is the spreading-out step for isomorphisms of fake elliptic curves carrying a full level-$m$ structure and an extra level-$\ell$ structure: an isomorphism defined over $L$ already exists over a finitely generated $R$-subalgebra of $L$, and the conclusion is phrased so as to descend to every ring under that subalgebra. It feeds the passage to directed colimits used in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_forall_isoTVia_of_isoTVia_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_forall_isoTVia_of_isoTVia_of_isPullbackVia
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
      ∀ (B : Type) [CommRing B] (φ : ↥T →+* B) (χ : R →+* B), φ.comp (algebraMap R ↥T) = χ →
        ∀ (uB wB : FakeEllipticCurve.WithFullLevel Λ N m B) (CuB : uB.1.ExtraLevel ℓ) (CwB : wB.1.ExtraLevel ℓ)
          (guB : uB.1.A ⟶ u.1.A) (gwB : wB.1.A ⟶ w.1.A),
        FakeEllipticCurve.IsPullbackVia χ u.1 uB.1 guB →
        (uB.2.P).1 ≫ guB = Spec.map (CommRingCat.ofHom χ) ≫ (u.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' uB.1.f),
          FactorsThrough CuB.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ guB) →
        FakeEllipticCurve.IsPullbackVia χ w.1 wB.1 gwB →
        (wB.2.P).1 ≫ gwB = Spec.map (CommRingCat.ofHom χ) ≫ (w.2.P).1 →
        (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t' wB.1.f),
          FactorsThrough CwB.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gwB) →
        ∃ (e : uB.1.A ≅ wB.1.A) (he : e.hom ≫ wB.1.f = uB.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia uB wB CuB CwB e he := by sorry
