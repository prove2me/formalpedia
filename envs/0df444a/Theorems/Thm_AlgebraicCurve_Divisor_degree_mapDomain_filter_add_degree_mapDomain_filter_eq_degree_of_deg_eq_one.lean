-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
-- name    : AlgebraicCurve.Divisor.degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/2ed99cfc-1fc1-5411-9fce-b876061b5086
-- title:
--   Degree of pushed-forward parts adds to degree, degree-one places
-- statement:
--   Let $K \subseteq F$ and $K' \subseteq F'$ be fields with $F$ a $K$-algebra and $F'$ a $K'$-algebra. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring; its degree is the $K$-dimension of the residue field of that local ring, a divisor is a finitely supported function from places to $\mathbb{Z}$, and the degree of a divisor is $\sum_V E(V)\,\deg V$. Assume every place of $F/K$ has degree $1$ and every place of $F'/K'$ has degree $1$. Let $r_1, r_2$ be arbitrary maps from the places of $F/K$ to the places of $F'/K'$, and let $p_1, p_2$ be decidable predicates on places of $F/K$ that are mutually exclusive, in the sense that $p_1 V$ implies $\lnot p_2 V$ for every $V$. Let $E$ be a divisor of $F/K$ each place in whose support satisfies $p_1$ or $p_2$. Then the degree of the push-forward along $r_1$ of the part of $E$ supported where $p_1$ holds, plus the degree of the push-forward along $r_2$ of the part where $p_2$ holds, equals the degree of $E$. Push-forward is `Finsupp.mapDomain`, i.e. coefficients are summed over fibres; no injectivity or finiteness is assumed of $r_1, r_2$.
--
--   This is the bookkeeping identity that the degrees of the two fibre parts of a divisor supported on two mutually exclusive classes of places add up to its total degree, in the situation where all places have degree one so that degree coincides with total coefficient mass. It is used by the common-unit/pole analysis for prolongation data on modular curves, in [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
    {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r₁ r₂ : Place K F → Place K' F') (p₁ p₂ : Place K F → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (hdisj : ∀ V, p₁ V → ¬ p₂ V)
    (E : Divisor K F) (hE : ∀ V ∈ E.support, p₁ V ∨ p₂ V) :
    Divisor.degree (Finsupp.mapDomain r₁ (E.filter p₁)) + Divisor.degree (Finsupp.mapDomain r₂ (E.filter p₂)) = E.degree := by sorry
