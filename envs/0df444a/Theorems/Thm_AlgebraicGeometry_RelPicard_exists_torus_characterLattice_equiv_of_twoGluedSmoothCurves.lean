-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cfe6a219-f251-5291-a60d-dbb495d3259e
-- title:
--   Split torus in Pic⁰ of a two-component curve
-- statement:
--   Let $k$ be an algebraically closed field, $x : X \to \operatorname{Spec} k$ a proper morphism with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions $C_j \to X$ over $\operatorname{Spec} k$ (so $i_j$ followed by $x$ is $c_j$) whose images jointly cover every point of $X$, with $C_1 \times_X C_2$ reduced and having exactly $s$ points, $s>0$. Let $\varepsilon$, $\varepsilon_1$, $\varepsilon_2$ be sections of $x$, $c_1$, $c_2$ over $\operatorname{Spec} k$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$, and let $D$, $D_1$, $D_2$ be pointed schemes over $k$ together with data $h_D$, $h_{D_1}$, $h_{D_2}$ representing, for $(X,\varepsilon)$, $(C_1,\varepsilon_1)$, $(C_2,\varepsilon_2)$ respectively, the functor of rigidified invertible modules on the fibre product whose restriction to every geometric fibre is algebraically equivalent to zero: each carries a Poincaré bundle satisfying that condition, a universal property classifying such bundles uniquely up to isomorphism, and the triviality of the pullback along the zero section. Let $\nu_1, \nu_2 : D \to D_1, D_2$ be morphisms over $\operatorname{Spec} k$, with $\nu_1$ the classifying morphism of the pullback of the Poincaré bundle of $D$ along $i_1$, and $\nu_2$ characterised pointwise: for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along the section $\varepsilon_2$ of the pullback, under the curve change map induced by $i_2$, of the bundle classified by $a$. Let $F$ be a field extension of $k$ in which every nonzero element has a divisor of degree zero with the prescribed orders at all places, let $S$ be a finite set of $s$ pairs of places of $F/k$, let $\mathrm{nd}$ be a bijection from $S$ to the set of $k$-points of $C_1 \times_X C_2$, and assume the two structure morphisms of $C_1 \times_X C_2$ agree. Let $\Phi$ be a bijection from $\mathrm{GluedPic}^0(k,F,S)$, the quotient of the group of admissible gluing data (a pair of divisors of degree zero vanishing at the marked places, together with units $w : S \to k^\times$ written additively) by the subgroup of glued principal data, onto the $k$-points of $D$, subject to: $\Phi$ is additive for the relative group law carried by $h_D$; for every $w$, the pullback of the Poincaré bundle of $D$ along $\Phi(\mathrm{nodeUnit}\,w)$ is a node-unit module for $X$, $i_1$, $i_2$ with the node sections coming from $\mathrm{nd}$ composed with the two projections and with gluing units the images of $w(\sigma)^{-1}$ in $\Gamma(\operatorname{Spec} k,\top)^\times$; and a class $g$ satisfies $\nu_1 \circ \Phi(g) = 1$ and $\nu_2 \circ \Phi(g) = 1$ exactly when $g$ lies in the range of $\mathrm{nodeUnit}$. The conclusion asserts the existence of a morphism $\tau$ from the split torus $\operatorname{Spec} k[\mathbb{Z}^{s-1}]$ to $D$ over $\operatorname{Spec} k$ and of an isomorphism of abelian groups $B$ from the character lattice of $S$ (the kernel of the sum-of-coordinates map on $S \to \mathbb{Z}$) onto $\mathbb{Z}^{s-1}$ such that: $\tau$ is a closed immersion; for all $\chi,\chi'$ in `WithConv (torusCoord k (s-1) →ₐ[k] k)`, the $k$-point of $D$ obtained from the product $\chi\chi'$ followed by $\tau$ is the relative group law product of those obtained from $\chi$ and from $\chi'$; for every $k$-scheme $t : T \to \operatorname{Spec} k$, a $T$-point $a$ of $D$ has both $a$ followed by $\nu_1$ and $a$ followed by $\nu_2$ equal to the respective units if and only if $a$ factors through $\tau$; and for every $k$-algebra map $\chi$ on the torus coordinate ring and every $w : S \to k^\times$, the point $\chi$ followed by $\tau$ equals $\Phi(\mathrm{nodeUnit}\,w)$ if and only if $\prod_\sigma w(\sigma)^{a(\sigma)} = \chi(X^{Ba})$ for every $a$ in the character lattice of $S$.
--
--   This identifies the toric part of the relative $\mathrm{Pic}^0$ of a curve with two smooth components meeting in $s$ points: the kernel of restriction to the two components is a closed split torus of rank $s-1$, and its $k$-points are matched, in an explicit basis of the degree-zero lattice on the set of nodes, with the node-unit classes in $\mathrm{GluedPic}^0(k,F,S)$. It is used in the analysis of the special fibre of the model of the modular curve, via [`ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre`](thm.html#ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus AlgebraicGeometry.TwoGluedCurves AlgebraicCurve ModularCurve

theorem AlgebraicGeometry.RelPicard.exists_torus_characterLattice_equiv_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (S : Finset (Place k F × Place k F)) (hS : S.card = s)
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (Φ : GluedPic0 k F S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)

    (hadd : ∀ a b, Φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (Φ a) (Φ b))

    (hnode : ∀ w : ↥S → Additive kˣ,
      IsNodeUnitModule x i₁ i₂
        (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
        (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
        (𝟙 (Spec (CommRingCat.of k)))
        (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
        (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).L)

    (hΦker : ∀ g : GluedPic0 k F S,
      (NeronModelInfra.schemeHomOverComp (Φ g) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one _ ∧
        NeronModelInfra.schemeHomOverComp (Φ g) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one _) ↔
        g ∈ (GluedPic0.nodeUnit S).range) :
    ∃ (τ : SchemeHomOver (torusStr k (s - 1)) D.toBase) (B : characterLattice ↥S ≃+ (Fin (s - 1) → ℤ)),
      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord k (s - 1) →ₐ[k] k),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) (χ * χ').ofConv) τ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) ∧

      (∀ (χ : torusCoord k (s - 1) →ₐ[k] k) (w : ↥S → Additive kˣ),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ) τ = Φ (GluedPic0.nodeUnit S w) ↔
          ∀ a : characterLattice ↥S,
            ((∏ σ, Additive.toMul (w σ) ^ (a : ↥S → ℤ) σ : kˣ) : k) = χ (AddMonoidAlgebra.single (B a) 1)) := by sorry
