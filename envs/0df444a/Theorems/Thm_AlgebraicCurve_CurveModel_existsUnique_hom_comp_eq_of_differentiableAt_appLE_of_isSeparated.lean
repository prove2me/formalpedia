-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated
-- name    : AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7fe757ea-0713-53fe-a473-48f59f7f09c3
-- title:
--   Holomorphic maps from the analytic model are algebraic
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure which is a function field in one variable, in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor of degree $0$ recording its orders at all places, each residue field of a place is finite over $\mathbb{C}$, and $\Omega_{F/\mathbb{C}}$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing $\mathbb{C}$, distinct from $F$, whose ring is a principal ideal ring. Suppose the set $\mathrm{Place}(\mathbb{C},F)$ carries a topology and a $\mathbb{C}$-charted structure making it a compact, Hausdorff, connected analytic one-dimensional complex manifold, and that this structure is analytically compatible with the arithmetic of $F$ in the following sense (hypothesis `hF`): for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{evalAt}_{\;\cdot}(f)$ read through the inverse extended chart at $v$ is meromorphic at the chart image of $v$ with meromorphic order equal to $\operatorname{ord}_v f = -\log$ of the adic valuation of $f$, where $\mathrm{evalAt}_v(f)$ is the residue of $f$ pulled back to $\mathbb{C}$ when $f$ lies in the valuation subring of $v$ and $0$ otherwise. Let $M$ be a `CurveModel ℂ F`: an integral scheme $M.C$ with a proper morphism $M.\mathrm{toBase}$ to $\operatorname{Spec}\mathbb{C}$, smooth of relative dimension one, together with an isomorphism of $F$ with the function field of $M.C$ over $\mathbb{C}$, a bijection between the closed points of $M.C$ and the places of $F$ identifying stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Let $pY : Y \to \operatorname{Spec}\mathbb{C}$ be separated and locally of finite type, and let $w$ assign to each place $v$ a $\mathbb{C}$-point of $Y$, i.e. a section of $pY$. Assume for every affine open $U \subseteq Y$ and every $\varphi \in \Gamma(Y,U)$ that the set of places $v$ whose point $w(v)$ factors through $U$ (the preimage of $U$ under $w(v)$ being all of $\operatorname{Spec}\mathbb{C}$) is open, and that there is a function $G : \mathrm{Place}(\mathbb{C},F) \to \mathbb{C}$ agreeing on that set with the value of $\varphi$ at $w(v)$, computed through `Scheme.appLE` and `Scheme.ΓSpecIso`, and such that for each $v$ in that set the composite of $G$ with the inverse extended chart at $v$ is complex-differentiable at the chart image of $v$. Then there is exactly one morphism $W : M.C \to Y$ with $W$ followed by $pY$ equal to $M.\mathrm{toBase}$ and such that for every $\mathbb{C}$-point $p$ of $M.C$ over $\operatorname{Spec}\mathbb{C}$, the composite of $p$ with $W$ is the point $w$ attached to the place corresponding to $p$ under `M.pointEquivPlace`.
--
--   This is the algebraicity (GAGA-type) statement for maps out of a curve: a map from the places of a complex function field in one variable to the $\mathbb{C}$-points of a separated scheme locally of finite type over $\mathbb{C}$, holomorphic when read through affine coordinates, is induced by a unique morphism of schemes from the smooth proper model, compatibly with the structure maps to $\operatorname{Spec}\mathbb{C}$. It is used in the construction of a morphism from a curve to an abelian scheme, where the analytically defined Abel–Jacobi map must be recognised as algebraic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry
open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated
    (F : Type) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (M : CurveModel ℂ F)
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pY] [LocallyOfFiniteType pY]
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (hw : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (φ : Γ(Y, U)),
      IsOpen {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} ∧
      ∃ G : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
          G v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U →
          DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
            (extChartAt 𝓘(ℂ, ℂ) v v)) :
    ∃! W : M.C ⟶ Y, W ≫ pY = M.toBase ∧
      ∀ p : {p : Spec (CommRingCat.of ℂ) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        p.1 ≫ W = (w (M.pointEquivPlace p)).1 := by sorry
