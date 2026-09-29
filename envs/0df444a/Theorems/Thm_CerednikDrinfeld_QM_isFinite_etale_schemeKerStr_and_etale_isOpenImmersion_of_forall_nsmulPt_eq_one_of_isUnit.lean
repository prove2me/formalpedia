-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
-- name    : CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/46feb4a4-f0c8-54f2-8efc-3652782406f1
-- title:
--   Closed N-torsion subscheme is étale and open in A[N]
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$ over $S$: for every $t : T \to \operatorname{Spec} S$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $S$-morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, the multiplication being natural in $T$. Assume $L$ is commutative, and that $f$ satisfies the bundle of abelian-scheme properties: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Let $\mathrm{lev} : C \to A$ be a closed immersion and $N$ a natural number such that every point $P$ of $A$ over any $t : T \to \operatorname{Spec} S$ which factors as $P_0$ followed by $\mathrm{lev}$ satisfies $N \cdot P = 1$ (iterated multiplication in the group law), with $\mathrm{lev}$ followed by $f$ flat and locally of finite presentation, and suppose the image of $N$ in $S$ is a unit. Then the structure morphism of $A[N]$, namely the second projection of the fibre product of the multiplication-by-$N$ map $A \to A$ (the $N$-th power of the identity point) and the unit section, is finite and étale; $\mathrm{lev}$ followed by $f$ is étale; and there is an identification of $\mathrm{lev}$ followed by multiplication by $N$ with $\mathrm{lev}$ followed by $f$ followed by the unit section, for which the induced morphism $C \to A[N]$ is an open immersion.
--
--   This is the standard statement that on an abelian scheme over a base in which $N$ is invertible the $N$-torsion subscheme is finite étale over the base, and that any closed, flat, finitely presented subscheme killed by $N$ is étale and open in it; it is stated here for bare data (a commutative relative group law together with smoothness, properness and connected fibres) rather than for a packaged fake elliptic curve. It is used in the analysis of level structures on quaternionic moduli, in particular to identify the geometric fibres of a level subgroup and to transport full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hcomm : L.IsCommutative) (hbundle : AbelianSchemePropertyBundle S f)
    {C : Scheme.{0}} (lev : C ⟶ A) (hlev_closed : IsClosedImmersion lev) (N : ℕ)
    (hlev_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (hlev_flat : Flat (lev ≫ f)) (hlev_fp : LocallyOfFinitePresentation (lev ≫ f))
    (hN : IsUnit ((N : ℕ) : S)) :
    IsFinite (L.schemeKerStr N) ∧ Etale (L.schemeKerStr N) ∧ Etale (lev ≫ f) ∧
      ∃ w : lev ≫ L.schemeNsmul N = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1,
        IsOpenImmersion (pullback.lift lev (lev ≫ f) w) := by sorry
