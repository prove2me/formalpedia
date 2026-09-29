-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_mapPt_of_isPullback_valuationSubring
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_mapPt_of_isPullback_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/14d53981-7a4d-51b6-b3ba-2dba26b7fd4a
-- title:
--   Extension of a level-compatible morphism stays level-compatible
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$, and let $O$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`. Given fake elliptic curves $\mathcal{A},\mathcal{D}$ of type $(\Lambda,N)$ over $O$ and $E,d$ of the same type over $\overline{\mathbb{Q}}$, assume: a morphism $g_E : E.A \to \mathcal{A}.A$ making the square with $E.f$, $\mathcal{A}.f$ and $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ cartesian, together with the hypothesis that for every scheme $T$, every $t' : T \to \mathrm{Spec}\,\overline{\mathbb{Q}}$ and every $T$-point $P$ of $E.A$ over $t'$, $P$ factors through $E.\mathrm{lev}$ exactly when there is $P_0 : T \to \mathcal{A}.C$ with $P_0$ followed by $\mathcal{A}.\mathrm{lev}$ equal to $P$ followed by $g_E$; the same data $g_d$ and level criterion for $d$ and $\mathcal{D}$; a morphism $\varphi : E.A \to d.A$ over $\overline{\mathbb{Q}}$ (i.e. $\varphi$ followed by $d.f$ is $E.f$) such that whenever a point $P$ of $E.A$ factors through $E.\mathrm{lev}$, the point $P$ followed by $\varphi$ factors through $d.\mathrm{lev}$; and a morphism $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ over $O$ with $g_E$ followed by $\Phi$ equal to $\varphi$ followed by $g_d$. Then for every scheme $T$, every $t : T \to \mathrm{Spec}\,O$ and every $T$-point $P$ of $\mathcal{A}.A$ over $t$ factoring through $\mathcal{A}.\mathrm{lev}$, the point $P$ followed by $\Phi$ factors through $\mathcal{D}.\mathrm{lev}$. Here "$P$ factors through $\mathrm{lev}$" means the existence of a lift of $P$ along $\mathrm{lev} : C \to A$.
--
--   This is the statement that a morphism over a valuation ring which extends a level-structure-preserving morphism on the generic fibre preserves level structures on all scheme-valued points, the structures on the generic fibre being identified with the generic fibres of the integral ones by the two cartesian squares. It feeds the construction of extra level structures and level isogenies over $O$ in the Čerednik–Drinfeld part of the argument, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback_valuationSubring_of_coprime_of_one_mem_of_isPullback_inf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_mapPt_of_isPullback_valuationSubring.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_mapPt_of_isPullback_valuationSubring
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough E.lev P ↔ ∃ P₀ : T ⟶ 𝒜.C, P₀ ≫ 𝒜.lev = P.1 ≫ gE)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_lev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' d.f),
      FactorsThrough d.lev P ↔ ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ gd)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough d.lev (mapPt φ hφ P))
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough 𝒜.lev P → FactorsThrough 𝒟.lev (mapPt Φ hΦ P) := by sorry
