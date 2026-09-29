-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
-- name    : AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/7a478896-27d1-5d89-a4ad-a614c27b81fd
-- title:
--   Algebraic coordinates of a holomorphic map to an affine open
-- statement:
--   Let $F$ be a field of characteristic-zero type over $\mathbb{C}$ that is finitely generated of transcendence degree one, in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place is $\operatorname{ord}_v f = -\log$ of the adic valuation of $f$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing $\mathbb{C}$, proper, and a principal ideal ring. Suppose the set $\mathrm{Place}\,\mathbb{C}\,F$ carries a topology and $\mathbb{C}$-charts making it a compact connected Hausdorff analytic one-dimensional manifold, and that (hypothesis `hF`) for every nonzero $f \in F$ and every place $v$ the chart expression $z \mapsto \operatorname{evalAt}_{\,\varphi^{-1}(z)} f$ is meromorphic at the centre $\varphi(v)$ with meromorphic order exactly $\operatorname{ord}_v f$, where $\operatorname{evalAt}_v$ sends $f$ in the valuation subring to the preimage in $\mathbb{C}$ of its residue class and $f$ outside it to $0$. Let $pY : Y \to \operatorname{Spec}\mathbb{C}$ be separated and locally of finite type, and let $w$ assign to each place $v$ a $\mathbb{C}$-point $w(v) : \operatorname{Spec}\mathbb{C} \to Y$ over $pY$. Assume (hypothesis `hw`) that for every affine open $U \subseteq Y$ and every $\phi \in \Gamma(Y,U)$ the locus of places $v$ with $w(v)$ factoring through $U$ is open, and there is a function $G$ on places which on that locus equals the value $\phi(w(v)) \in \mathbb{C}$, obtained from $\phi$ by the restriction map of $w(v)$ and the identification of $\Gamma(\operatorname{Spec}\mathbb{C},\top)$ with $\mathbb{C}$, and whose chart expression is complex differentiable at $\varphi(v)$ for each such $v$. Then for every affine open $U$ which at least one place hits and every $\phi \in \Gamma(Y,U)$ there is a unique $\xi \in F$ such that for all places $v$ with $w(v)$ in $U$ one has $\xi$ in the valuation subring of $v$ and $\operatorname{evalAt}_v \xi = \phi(w(v))$.
--
--   This is the algebraisation step for maps from the Riemann surface of a one-dimensional function field: the coordinate functions of a holomorphic $w$ on the locus lying over an affine open are realised by unique elements of $F$, regular at every place of that locus. It is used by [`AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated`](thm.html#AlgebraicCurve.CurveModel.existsUnique_hom_comp_eq_of_differentiableAt_appLE_of_isSeparated) to produce a scheme morphism from the analytic data, and it rests on the finiteness of the locus where $w$ misses $U$ together with the identification of meromorphic functions on the surface with elements of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt
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
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : ∃ v : Place ℂ F, ⊤ ≤ (w v).1 ⁻¹ᵁ U) (φ : Γ(Y, U)) :
    ∃! ξ : F, ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧ Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ) := by sorry
