-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
-- name    : AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/0d500a62-b019-5cd7-ac9d-e358371fa8ff
-- title:
--   Dichotomy for the places missing an affine open
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure which is a function field of one variable over $\mathbb{C}$ in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over the intermediate field $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $v.\mathrm{ord}\,f$, every residue field of a place is finite over $\mathbb{C}$, and $\Omega_{F/\mathbb{C}}$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing the image of $\mathbb{C}$, distinct from $F$ itself, and a principal ideal ring. The set $\mathrm{Place}(\mathbb{C},F)$ carries a topology, an atlas of $\mathbb{C}$-valued charts making it a compact, Hausdorff, connected analytic ($\omega$) manifold over $\mathbb{C}$, and it is assumed (hypothesis `hF`) that for each nonzero $f \in F$ and each place $v$ the function $z \mapsto \mathrm{evalAt}\,\bigl((\mathrm{extChartAt}\ v)^{-1}z\bigr)\,f$ is meromorphic at the chart image of $v$ with meromorphic order equal to $v.\mathrm{ord}\,f$. Let $p_Y : Y \to \operatorname{Spec}\mathbb{C}$ be a separated, locally of finite type morphism of schemes, and let $w$ assign to every place $v$ a $\mathbb{C}$-point of $Y$, namely a section $P : \operatorname{Spec}\mathbb{C} \to Y$ of $p_Y$. Assume that for every affine open $U \subseteq Y$ and every $\varphi \in \Gamma(Y,U)$ the set of places $v$ for which the scheme-theoretic preimage $(w\,v)^{-1}U$ is the whole of $\operatorname{Spec}\mathbb{C}$ is open, and there is a function $G : \mathrm{Place}(\mathbb{C},F) \to \mathbb{C}$ which on that set is given by the pullback of $\varphi$ along $w\,v$, transported through the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C},\top) \cong \mathbb{C}$, and which at each such $v$ is complex-differentiable in the chart at $v$. Then for every affine open $U \subseteq Y$: either no place $v$ satisfies $(w\,v)^{-1}U = \top$, or the set of places $v$ failing this condition is finite.
--
--   This is the finiteness step in extending a chartwise holomorphic map from the compact Riemann surface of places of $F$ to a separated scheme $Y$: by the identity principle on charts together with connectedness, the locus of places whose $\mathbb{C}$-point falls outside a given affine open $U$ is either all of the surface or discrete, hence finite. It is used in the construction of the unique morphism from the curve model to $Y$ ([`AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated`](thm.html#AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated)) and in [`AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt`](thm.html#AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt), and it cites the manifold identity principle [`Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected`](thm.html#Manifold.forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.forall_not_le_preimage_or_finite_setOf_of_differentiableAt_appLE_of_isSeparated
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
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pY] [LocallyOfFiniteType pY]
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (hw : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (φ : Γ(Y, U)),
      IsOpen {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} ∧
      ∃ G : Place ℂ F → ℂ,
        (∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
          G v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) ∧
        ∀ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U →
          DifferentiableAt ℂ (fun z : ℂ => G ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
            (extChartAt 𝓘(ℂ, ℂ) v v))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    (∀ v : Place ℂ F, ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)) ∨ Set.Finite {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)} := by sorry
