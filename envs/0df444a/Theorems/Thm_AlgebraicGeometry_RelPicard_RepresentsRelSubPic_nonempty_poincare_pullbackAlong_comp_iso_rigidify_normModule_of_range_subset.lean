-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/faa94ae1-c5fb-5148-abc4-90c1754ee509
-- title:
--   Norm description of the Poincaré bundle under arbitrary base change
-- statement:
--   Fix a commutative ring $R$, schemes $C,C'$ with structure morphisms $c\colon C\to\operatorname{Spec}R$, $c'\colon C'\to\operatorname{Spec}R$, and a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec R)) c`, i.e. a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity). Let $P$ be a `SubPicCondition` for $(c,\varepsilon)$, that is a property of $\varepsilon$-rigidified invertible modules on $C\times_R T$ containing the unit, invariant under isomorphism of underlying modules and stable under pullback, let $D$ be a `RelativePic0Designation` (a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}R$ and a zero section), and let $h$ witness that $D$ represents $P$: it provides a rigidified bundle $h.\mathrm{poincare}$ on $C\times_R D$ satisfying $P$, the universal bijection between $P$-bundles over $t$ and morphisms over $\operatorname{Spec}R$ from the base of $t$ to $D$, and triviality along the zero section. Let $\pi_a,\pi_b\colon C'\to C$ be morphisms over $\operatorname{Spec}R$ with $\pi_a$ finite and locally of finite presentation. Let $U\subseteq C$ be open and $d\in\mathbb N$ with $\pi_a\mid_U$ flat and $\pi_a$ of fibre rank $d$ at every point of $U$. Let $\mathcal N$ be an invertible module on $C\times_R D$ such that for every open $V\subseteq C\times_R D$ and every $d'$, if the base change $\pi_a\times D$ restricted over $V$ is flat, locally of finite presentation and of constant fibre rank $d'$, then $\mathcal N|_V$ is isomorphic to $\mathrm{normModule}$ of rank $d'$ of the restriction to $(\pi_a\times D)^{-1}V$ of $(\pi_b\times D)^{*}h.\mathrm{poincare}.L$, where $\mathrm{normModule}\,\pi\,d'\,L=\det_{d'}(\pi_*L)\otimes\det_{d'}(\pi_*\mathcal O)^{\vee}$. Let $T$ be an endomorphism of $D$ over $\operatorname{Spec}R$ such that the pullback of $h.\mathrm{poincare}$ along $T$ has underlying module isomorphic to $\mathrm{rigidify}$ of $\mathcal N$ along the rigidifying section $\mathrm{rigSection}\,c\,D.\mathrm{toBase}\,\varepsilon$ and the projection $C\times_RD\to D$, i.e. $\mathcal N$ tensored with the pullback of the dual of its restriction along that section. Then for every scheme $T'$ with structure morphism $t\colon T'\to\operatorname{Spec}R$ and every morphism $a\colon T'\to D$ over $\operatorname{Spec}R$ such that the set-theoretic image of the projection $C\times_RT'\to C$ is contained in $U$, the underlying module of the pullback of $h.\mathrm{poincare}$ along $a$ followed by $T$ is isomorphic to the $\varepsilon$-rigidification, over $t$, of the rank-$d$ norm along $\pi_a\times T'$ of the pullback along $\pi_b\times T'$ of the underlying module of the pullback of $h.\mathrm{poincare}$ along $a$; the assertion is the nonemptiness of the type of such isomorphisms.
--
--   This is the base-change step that propagates a norm (correspondence) description of an endomorphism of the representing scheme from the universal point to an arbitrary point: knowing the formula for the Poincaré bundle twisted by $T$ over $D$ itself, one obtains it over every base on which the relevant projection lands in the flat locus of $\pi_a$. It is used in the construction of Hecke operators on the relative Jacobians of modular curves, where $\pi_a,\pi_b$ are the two degeneracy maps of a Hecke correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D)

    (πa πb : SchemeHomOver c' c) [IsFinite πa.1] [LocallyOfFinitePresentation πa.1]

    (U : C.Opens) (d : ℕ) (hfl : Flat (πa.1 ∣_ U)) (hrk : ∀ y : C, y ∈ U → πa.1.finrank y = d)

    (𝒩 : (pullback c D.toBase).Modules) (h𝒩 : Scheme.Modules.IsInvertible 𝒩)
    (hNe : ∀ (V : (pullback c D.toBase).Opens) (d' : ℕ),
      Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πa.1 πa.2 D.toBase) ∣_ V) →
      (∀ y : V, ((curveChange πa.1 πa.2 D.toBase) ∣_ V).finrank y = d') →
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
        Scheme.Modules.normModule ((curveChange πa.1 πa.2 D.toBase) ∣_ V) d'
          ((Scheme.Modules.pullback ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι).obj
            ((Scheme.Modules.pullback (curveChange πb.1 πb.2 D.toBase)).obj h.poincare.L))))

    (T : SchemeHomOver D.toBase D.toBase)
    (hT : Nonempty ((h.poincare.pullbackAlong T).L ≅
      Scheme.Modules.rigidify (rigSection c D.toBase ε) (pullback.snd c D.toBase) 𝒩))

    {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase)
    (hU : Set.range (pullback.fst c t).base ⊆ (U : Set C)) :
    Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        (Scheme.Modules.normModule (curveChange πa.1 πa.2 t) d
          ((Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L))) := by sorry
