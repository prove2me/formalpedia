-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex
-- name    : AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/acd06688-0825-5bd9-92ef-fad9333abe53
-- title:
--   Finitely many parameter discs cover every place
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, and assume that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x)$, and that `IsCurveOver ℂ F` holds, i.e. every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place is $\operatorname{ord}_v f$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place $v$ is a valuation subring of $F$ containing $\mathbb{C}$, different from $F$ and a principal ideal ring; $\operatorname{ord}_v$ is the associated normalised $\mathbb{Z}$-valued order function, and $f(v) :=$ `Place.evalAt v f` is the image in $\mathbb{C}$ of the residue class of $f$ when $f$ lies in the valuation ring, and $0$ otherwise. Suppose given, for each place $v$, a radius $\rho v > 0$, a map $\gamma v : \mathbb{C} \to \{\text{places}\}$ and an element $t v \in F$ such that $\gamma v (0) = v$; for all $z$ with $|z| < \rho v$ one has $\operatorname{ord}_{\gamma v (z)}(t v - z) = 1$; and for every nonzero $f \in F$ and every such $z$ the function $u \mapsto f(\gamma v (u))$ is meromorphic at $z$, its meromorphic order at $z$ equals $\operatorname{ord}_{\gamma v (z)} f$, and it is analytic at $z$ whenever $\operatorname{ord}_{\gamma v (z)} f \ge 0$. Then there exist a finite set $S$ of places and a function $r$ on places with $0 \le r v < \rho v$ for all $v \in S$, such that every place $w$ of $F$ is of the form $\gamma v (z)$ for some $v \in S$ and some $z \in \mathbb{C}$ with $\|z\| \le r v$.
--
--   This is the compactness of the Riemann surface attached to a function field in one variable over $\mathbb{C}$, expressed as the existence of a finite subcover of the given family of analytic parameter discs by closed subdiscs. It is used in the construction of the charted-space structure on the set of places with the order–meromorphic order compatibility, and in the extraction of convergent subsequences of evaluation maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (ρ : Place ℂ F → ℝ) (γ : Place ℂ F → ℂ → Place ℂ F) (t : Place ℂ F → F)
    (hρ : ∀ v, 0 < ρ v) (h₀ : ∀ v, γ v 0 = v)
    (ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1)
    (hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
        MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)) :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ γ v z = w := by sorry
