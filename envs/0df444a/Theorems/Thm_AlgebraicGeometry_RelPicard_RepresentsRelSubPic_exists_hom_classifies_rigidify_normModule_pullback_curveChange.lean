-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_normModule_pullback_curveChange
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_normModule_pullback_curveChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a50d8939-6739-5ea3-9f4f-6fdfb75d7fb7
-- title:
--   Correspondence-induced endomorphism of the representing object of relative Pic⁰
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme with a morphism $c : C \to \operatorname{Spec} R$, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$. Let $D$ be a `RelativePic0Designation` for $c$: a scheme $D.P$ with a structure morphism $D.\mathrm{toBase} \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. Assume $h$ witnesses that $D$ represents the functor of rigidified invertible modules for $(c,\varepsilon)$ cut out by `algEquivZeroCut`, namely: $h.\mathrm{poincare}$ is a rigidified invertible module on $C \times_{\operatorname{Spec} R} D.P$ satisfying `FibrewiseAlgEquivZero` (for every algebraically closed field $k$ and every $k$-point of the base the restriction to the corresponding fibre of $C$ is `IsAlgEquivZero`), every rigidified invertible module over a base $t : T \to \operatorname{Spec} R$ with that fibrewise property is induced by a unique morphism $T \to D.P$ over $\operatorname{Spec} R$ up to isomorphism of underlying modules, and the pullback of $h.\mathrm{poincare}$ along the zero section is isomorphic to the unit module. Let $E$ be a scheme with $y : E \to \operatorname{Spec} R$ and two morphisms $p, e : E \to C$ over $\operatorname{Spec} R$, i.e. $p \circ c = y = e \circ c$ (diagrammatically $p \mathbin{≫} c = y$, $e \mathbin{≫} c = y$), with $p$ finite, flat and locally of finite presentation, and suppose $p$ has constant rank: $p.\mathrm{finrank}\,x = d$ for all $x \in C$ and a fixed $d \in \mathbb{N}$. The conclusion asserts the existence of an endomorphism $u$ of $D.P$ over $\operatorname{Spec} R$ (a morphism $u$ with $u \mathbin{≫} D.\mathrm{toBase} = D.\mathrm{toBase}$) such that for every scheme $S$, every $t : S \to \operatorname{Spec} R$ and every $b : S \to D.P$ over $\operatorname{Spec} R$, the underlying module of the pullback of $h.\mathrm{poincare}$ along $b$ followed by $u$ is isomorphic, on $C \times_{\operatorname{Spec} R} S$, to the rigidification along `rigSection c t ε` (tensoring with the $\mathrm{pr}_S$-pullback of the dual of the restriction along that section) of the norm module `normModule` of $d$-th determinants along the finite flat map $E \times_{\operatorname{Spec} R} S \to C \times_{\operatorname{Spec} R} S$ induced by $p$, applied to the pullback along the map induced by $e$ of the underlying module of the pullback of $h.\mathrm{poincare}$ along $b$. Only existence of an isomorphism for each $b$ is asserted, with no uniqueness of $u$ and no compatibility between the isomorphisms for varying $b$.
--
--   This is the construction, on the scheme representing the fibrewise algebraically trivial rigidified relative Picard functor of $(C,\varepsilon)$, of the endomorphism induced by the correspondence $p, e : E \rightrightarrows C$ by the rule $L \mapsto \mathrm{Nm}_p(e^*L)$, with no representability assumed for the Picard functor of $E$. It feeds the variant which in addition records the composition identity for such classifying morphisms, and thereby the Hecke and Frobenius action on relative Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_normModule_pullback_curveChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_normModule_pullback_curveChange
    {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {E : Scheme.{u}} (y : E ⟶ Spec (CommRingCat.of R)) (p e : E ⟶ C) (hp : p ≫ c = y) (he : e ≫ c = y)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] (d : ℕ) (hd : ∀ x : C, p.finrank x = d) :
    ∃ u : SchemeHomOver D.toBase D.toBase,
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
          Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
            (Scheme.Modules.normModule (curveChange (c := c) (c' := y) p hp t) d
              ((Scheme.Modules.pullback (curveChange (c := c) (c' := y) e he t)).obj
                (h.poincare.pullbackAlong b).L))) := by sorry
