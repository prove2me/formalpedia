-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong
-- name    : AlgebraicCurve.CurveModel.nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bc49a0d7-d0a7-582a-96cd-c8252cd59df7
-- title:
--   Pull-back of a point ideal sheaf is the conorm
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields, each a $k$-algebra in which every nonzero element has a degree-zero divisor recording its orders at all places (`HasPrincipalDivisors`). Let $M$ and $M'$ be curve models of $F$ and $F'$ over $k$: integral schemes $M.C$, $M'.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with identifications of $F$, resp. $F'$, with the function field compatible with $k$, and bijections of closed points with places matching stalks to valuation subrings. Let $\varphi : F \to F'$ be a $k$-algebra map whose underlying ring map is integral, and let $g : M'.C \to M.C$ satisfy $M.\mathrm{toBase} \circ g = M'.\mathrm{toBase}$ and read $\varphi$ on $k$-points: for every section $x'$ of $M'.\mathrm{toBase}$, the place of $M$ attached to $g \circ x'$ is the restriction along $\varphi$ of the place attached to $x'$. Let $gk$ be a morphism from the fibre product of $M'.\mathrm{toBase}$ with $\mathrm{id}_{\operatorname{Spec} k}$ to that of $M.\mathrm{toBase}$ with $\mathrm{id}_{\operatorname{Spec} k}$ commuting with both projections, $g$ on the first and the identity on the second, and let $x$ be a section of $M.\mathrm{toBase}$. Then there exists an isomorphism of modules over the fibre product for $M'$ between the $gk$-pull-back of the module of the ideal sheaf of the graph of $x$ (the relative effective Cartier divisor `RelEffCartierDiv.ofPoint M.toBase x.1 x.2`, whose module is the kernel of the unit to the pushforward along the closed immersion) and the iterated tensor product, folded from the right starting at the monoidal unit along the list of elements of the finite set of places $W$ of $F'$ whose restriction along $\varphi$ is the place of $x$, of the modules of the $e_W$-th powers of the ideal sheaves of the corresponding points of $M'$, where $e_W$ is the ramification index of $W$ along $\varphi$. Only the existence of such an isomorphism is asserted.
--
--   This is the statement that the pull-back of a point divisor along a finite morphism of smooth proper curves is the conorm divisor $\sum_{W \mid v} e(W\mid v)\,W$, formulated for the invertible ideal sheaves of the relative effective Cartier divisors cut out by $k$-points. It feeds the corresponding statement for a formal sum of points and, through that, the computation of points of the relative Picard scheme of a model of $X_1(p)$ in terms of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicCurve

theorem AlgebraicCurve.CurveModel.nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ)

    (gk : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback M.toBase (𝟙 (Spec (CommRingCat.of k))))
    (hgk₁ : gk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g) (hgk₂ : gk ≫ pullback.snd _ _ = pullback.snd _ _)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    Nonempty ((Scheme.Modules.pullback gk).obj (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.module ≅
      ((Place.fiberAlong φ hφ (M.pointEquivPlace x)).toList.foldr
        (fun W N => ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1 (M'.pointEquivPlace.symm W).2).I ^
          (Place.ramificationIndexAlong φ W)).module ⊗ N)
        (𝟙_ (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by sorry
