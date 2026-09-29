-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
-- name    : CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ab459367-2098-5f71-a9d4-93ff8902f858
-- title:
--   Finite étale d-torsion of a closed N-torsion subscheme
-- statement:
--   Let $S$ be a commutative ring and $f : A \to \operatorname{Spec} S$ a morphism of schemes equipped with a relative group law $L$, i.e. a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverse, naturality of multiplication) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over each $t : T \to \operatorname{Spec} S$; assume $L$ is commutative and that $f$ satisfies the bundle of properties consisting of smoothness, properness, connectedness of all fibres and the existence of a relative group law. Let $\mathrm{lev} : C \to A$ be a closed immersion and $N$ a natural number such that every point $P$ over any $t$ which factors as $P = \mathrm{lev} \circ P_0$ satisfies $N \cdot P = 1$ (iterated $L$-multiplication), with $C \to \operatorname{Spec} S$ flat and locally of finite presentation, and suppose the image of $N$ in $S$ is a unit. Let $d \mid N$, write $[d] : A \to A$ for the morphism obtained by applying the $d$-fold $L$-sum to the tautological point, and let $A[d]$ be the fibre product of $[d]$ with the unit section $\operatorname{Spec} S \to A$. Then the composite $Y := C \times_A A[d] \to C \to \operatorname{Spec} S$ is finite and étale, the projection $Y \to C$ is an open immersion, and for every $S$-scheme $t : T \to \operatorname{Spec} S$ and every point $P$ of $A$ over $t$, the point $P$ factors through $Y \to C \to A$ if and only if $P$ factors through $\mathrm{lev}$ and $d \cdot P = 1$.
--
--   This is the standard statement that, for $N$ invertible on the base, the $d$-torsion of a flat, finitely presented closed $N$-torsion subscheme of an abelian scheme is finite étale over the base, open in the given subscheme, together with the description of its functor of points. It is used in the construction of level structures on fake elliptic curves and in the count showing that the group of $d$-torsion points cut out by such a level subscheme has order $d^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.isFinite_etale_pullback_schemeKer_and_factorsThrough_iff_of_dvd_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
    {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
    (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
    (hN : IsUnit ((N : ℕ) : S)) (d : ℕ) (hd : d ∣ N) :
    IsFinite (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev ≫ f) ∧
    Etale (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev ≫ f) ∧
    IsOpenImmersion (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1)) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough (pullback.fst lev (pullback.fst (L.schemeNsmul d) (L.one (𝟙 (Spec (CommRingCat.of S)))).1) ≫ lev) P ↔
        FactorsThrough lev P ∧ nsmulPt L t d P = L.one t := by sorry
