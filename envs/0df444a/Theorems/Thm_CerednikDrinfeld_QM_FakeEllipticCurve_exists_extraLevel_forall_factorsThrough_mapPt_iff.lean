-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a1d08bf5-373f-5719-a19e-accde46bbbc3
-- title:
--   Transport of an extra level along an isomorphism of fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$ and a natural number $\ell$. Let $E'$ and $E$ be fake elliptic curves of type `FakeEllipticCurve Λ N S`, i.e. schemes $E'.A$, $E.A$ over $\operatorname{Spec} S$ carrying commutative relative group laws, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ and level data. Let $e : E'.A \cong E.A$ be an isomorphism of schemes with $e.\mathrm{hom}$ followed by $E.f$ equal to $E'.f$, so that composition with $e.\mathrm{hom}$ carries a point of $E'$ over any $t : T \to \operatorname{Spec} S$ (a morphism $T \to E'.A$ over $t$) to a point of $E$ over $t$; this is the operation `mapPt e.hom he`. Assume: this operation is multiplicative for the two relative group laws on all test bases; $E'.\mathrm{act}\,x$ followed by $e.\mathrm{hom}$ equals $e.\mathrm{hom}$ followed by $E.\mathrm{act}\,x$ for every $x \in \Lambda$; and, for every $t$ and every point $P$ of $E'$ over $t$, $P$ factors through the level morphism $E'.\mathrm{lev}$ exactly when `mapPt e.hom he P` factors through $E.\mathrm{lev}$ (factoring through a morphism $\mathrm{lev} : C \to A$ meaning that the point is $P_0$ followed by $\mathrm{lev}$ for some $P_0 : T \to C$). Let $K'$ be an extra level at $\ell$ on $E'$: a scheme with a closed immersion into $E'.A$ whose points form a subgroup containing the unit, killed by $\ell$, stable under $\Lambda$, meeting the level data only in the unit, finite flat and locally of finite presentation of rank $\ell^2$ over $S$, with geometric fibres isomorphic as groups to $(\mathbb{Z}/\ell)^2$. Then there is an extra level $K$ at $\ell$ on $E$ such that, for every $t : T \to \operatorname{Spec} S$ and every point $P$ of $E'$ over $t$, the point `mapPt e.hom he P` factors through $K.\mathrm{levK}$ if and only if $P$ factors through $K'.\mathrm{levK}$.
--
--   This is the transport of a level structure along an isomorphism in the sense of Katz–Mazur, in the explicit form in which the resulting subgroup scheme of $E$ is pinned down pointwise by the given isomorphism $e$, rather than merely asserting an abstract isomorphism of pairs $(E',K') \cong (E,K)$. It is used in the representability and moduli statements for fake elliptic curves with extra level at $\ell$, in particular in the construction of fine and coarse moduli and in the orbit counts under the automorphisms of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_mapPt_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (E' E : FakeEllipticCurve Λ N S) (e : E'.A ≅ E.A) (he : e.hom ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt e.hom he (E'.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E'.act x ≫ e.hom = e.hom ≫ E.act x)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      FactorsThrough E'.lev P ↔ FactorsThrough E.lev (mapPt e.hom he P))
    (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
        FactorsThrough K.levK (mapPt e.hom he P) ↔ FactorsThrough K'.levK P := by sorry
