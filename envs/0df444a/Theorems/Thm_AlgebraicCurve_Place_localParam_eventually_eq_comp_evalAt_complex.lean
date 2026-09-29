-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex
-- name    : AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/88265c74-e6df-546c-8c77-c43d5e6e5dae
-- title:
--   Uniqueness of the analytic branch through a complex place
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure and satisfying `IsCurveOver ℂ F`: every nonzero $f \in F$ has a principal divisor of degree $0$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$. Here a place of $F$ over $\mathbb{C}$ is a valuation subring of $F$ containing $\mathbb{C}$, distinct from $F$ itself, whose ring is a principal ideal ring; for a place $v$, $\operatorname{ord}_v f$ is minus the logarithm of the associated adic valuation of $f$, and $v.\mathrm{evalAt}(f) \in \mathbb{C}$ is the preimage under $\mathbb{C} \to \kappa(v)$ of the residue class of $f$ when $f$ lies in the valuation subring, and $0$ otherwise. Given two maps $\gamma, \gamma' : \mathbb{C} \to \operatorname{Place} \mathbb{C} F$, an element $t \in F$, sets $U \in \mathcal{N}(z_0)$ and $U' \in \mathcal{N}(z_0')$ with $\gamma'(z_0') = \gamma(z_0)$, assume: $\operatorname{ord}_{\gamma(z)}(t - z) = 1$ for all $z \in U$; and that for each nonzero $f \in F$ and each $z$ in $U$ (respectively $U'$) the function $u \mapsto \mathrm{evalAt}_{\gamma(u)}(f)$ (respectively with $\gamma'$) is meromorphic at $z$, its meromorphic order at $z$ equals $\operatorname{ord}_{\gamma(z)} f$ (respectively $\operatorname{ord}_{\gamma'(z)} f$), and it is analytic at $z$ whenever that order is non-negative. Then for all $z$ in some neighbourhood of $z_0'$ one has $\gamma'(z) = \gamma\bigl(\mathrm{evalAt}_{\gamma'(z)}(t)\bigr)$.
--
--   This is the uniqueness of the analytic branch of places through a given place: any second analytic parametrisation of the places of $F$ agrees, near the base point, with the first one after reparametrising by the local coordinate $t$. It is used in the construction of a charted space structure on the places of a complex function field, namely by [`AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`](thm.html#AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex), where it supplies the compatibility of candidate charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (γ γ' : ℂ → Place ℂ F) (t : F) (U U' : Set ℂ) (z₀ z₀' : ℂ)
    (hU : U ∈ 𝓝 z₀) (hU' : U' ∈ 𝓝 z₀') (h₀ : γ' z₀' = γ z₀)
    (ht : ∀ z ∈ U, (γ z).ord (t - algebraMap ℂ F z) = 1)
    (hγ : ∀ f : F, f ≠ 0 → ∀ z ∈ U,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z))
    (hγ' : ∀ f : F, f ≠ 0 → ∀ z ∈ U',
        MeromorphicAt (fun u : ℂ => (γ' u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ' u).evalAt f) z = ((γ' z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ' z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ' u).evalAt f) z)) :
    ∀ᶠ z in 𝓝 z₀', γ' z = γ ((γ' z).evalAt t) := by sorry
