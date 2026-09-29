-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
-- name    : AlgebraicCurve.CurveModel.exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a82d48fc-5e74-5d39-82f6-7f8a9bea92b9
-- title:
--   Local holomorphic lifting of a curve map to ℂ^g
-- statement:
--   Fix a scheme $G$ with a separated structure morphism $f : G \to \operatorname{Spec}\mathbb{C}$, a natural number $g$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{C}^g$, and a bijection $e$ between the sections of $f$ over $\operatorname{Spec}\mathbb{C}$ (morphisms $\varphi : \operatorname{Spec}\mathbb{C} \to G$ with $\varphi \circ f$ the identity) and $\mathbb{C}^g/\Lambda$. Assume: (hL1) $\Lambda$ is the $\mathbb{Z}$-span of the range of an $\mathbb{R}$-basis of $\mathbb{C}^g$ indexed by $\mathrm{Fin}(2g)$; (hAN) for every open $U \subseteq G$ and every $\varphi \in \Gamma(G,U)$ the set $S_U$ of $v \in \mathbb{C}^g$ for which the point $e^{-1}([v])$ factors through $U$ (its scheme-theoretic preimage of $U$ is all of $\operatorname{Spec}\mathbb{C}$) is open, and there is $F : \mathbb{C}^g \to \mathbb{C}$, complex differentiable on $S_U$, whose value at $v$ is the pullback of $\varphi$ along $e^{-1}([v])$ read through $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$; (hCOV) for every $v_0 \in \mathbb{C}^g$ there are an open $U$, sections $t_1,\dots,t_g \in \Gamma(G,U)$, $\varepsilon > 0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^g$ and $F : \mathbb{C}^g \to \mathbb{C}^g$ such that all points of the $\varepsilon$-ball about $v_0$ give points factoring through $U$, $F$ agrees there with $v \mapsto (t_i$ evaluated at $e^{-1}([v]))_i$, and $F$ has Fréchet derivative $D$ at $v_0$. Let $F$ be a field extension of $\mathbb{C}$ which is finite over $\mathbb{C}(x)$ for some transcendental $x$, satisfying `IsCurveOver` $\mathbb{C}$ $F$ (every nonzero element has a degree-zero divisor given by the orders $\operatorname{ord}_v$, every residue field is finite over $\mathbb{C}$, and $\Omega_{F/\mathbb{C}}$ is free of rank one), with the space of places $\operatorname{Place}(\mathbb{C},F)$ carrying a compact, Hausdorff, connected analytic manifold structure charted on $\mathbb{C}$, such that (hF) for every nonzero $h \in F$ and every place $v$ the function $z \mapsto \operatorname{evalAt}_{(\mathrm{ext chart})^{-1}(z)}(h)$ is meromorphic at the chart image of $v$ with meromorphic order $\operatorname{ord}_v(h)$. Let $M$ be a `CurveModel` of $F$ over $\mathbb{C}$, i.e. an integral scheme $M.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec}\mathbb{C}$ together with an isomorphism of $F$ with its function field over $\mathbb{C}$, a bijection of its closed points with the places matching stalks and valuation rings, and the property that every finite set of points lies in an affine open. Let $\nu : M.C \to G$ satisfy $\nu$ followed by $f$ equal to the structure morphism of $M.C$, let $v_0$ be a place and $w_0 \in \mathbb{C}^g$ with $e$ of the image under $\nu$ of the $\mathbb{C}$-point of $M.C$ corresponding to $v_0$ equal to the class $[w_0]$. Then there are $\varepsilon > 0$ and $vl : \mathbb{C} \to \mathbb{C}^g$ such that the $\varepsilon$-ball about the chart image of $v_0$ lies in the chart target, $vl$ is complex differentiable on that ball, $vl$ takes the value $w_0$ at the chart image of $v_0$, and for every $z$ in the ball the image under $e \circ \nu$ of the $\mathbb{C}$-point corresponding to the place with chart coordinate $z$ is the class $[vl(z)]$.
--
--   This is the statement that an algebraic morphism from a complete smooth curve to a scheme whose complex points are uniformised by $\mathbb{C}^g/\Lambda$ lifts, locally in a chart on the Riemann surface of places, to a holomorphic map into the universal cover $\mathbb{C}^g$, with a prescribed lift of the image of the base point. It is used in the construction of morphisms from curves to abelian schemes compatible with the uniformisation, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra AlgebraicCurve CerednikDrinfeld.QM
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.CurveModel.exists_differentiableOn_lift_pointEquiv_comp_of_differentiableOn_appLE_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f] {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ)))
    (hCOV : ∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀)
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
    (ν : M.C ⟶ G) (hν : ν ≫ f = M.toBase)
    (v₀ : Place ℂ F) (w₀ : Fin g → ℂ)
    (hw₀ : e (mapPt ν hν (M.pointEquivPlace.symm v₀)) = (w₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)) :
    ∃ (ε : ℝ) (vl : ℂ → (Fin g → ℂ)), 0 < ε ∧
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε ⊆ (extChartAt 𝓘(ℂ, ℂ) v₀).target ∧
      DifferentiableOn ℂ vl (Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε) ∧
      vl (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) = w₀ ∧
      ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v₀ v₀) ε,
        e (mapPt ν hν (M.pointEquivPlace.symm ((extChartAt 𝓘(ℂ, ℂ) v₀).symm z))) =
          (vl z : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by sorry
