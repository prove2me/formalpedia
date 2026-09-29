-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
-- name    : AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c2b96ca9-9c56-5313-ba67-f837e6bf3440
-- title:
--   Place at a rational point of the t-chart is centred
-- statement:
--   Let $K$ be a field and $L$ a field extension of $K$ (in the same universe), let $t \in L$ be nonzero and suppose $L$ is finite-dimensional over the intermediate field $K\langle t\rangle$. Write $C =$ `glued K t` for the scheme obtained as the pushout of the two chart maps of the two-chart model attached to $t$, and let `chartRing K ({t} : Set L)` denote the $K$-subalgebra of $L$ consisting of the elements integral over $K[t] =$ `Algebra.adjoin K {t}`. Let $P$ assign to each closed point $x$ of $C$ a place of $L/K$, that is a valuation subring of $L$ containing $\operatorname{im}(K \to L)$, distinct from $L$ and a principal ideal ring, and assume that for every closed point $x$ the image in $L$ of the local ring $\mathcal{O}_{C,x}$ — taken through the canonical map $\mathcal{O}_{C,x} \to \mathrm{Frac}(C)$ followed by the inverse of the identification `gluedFunctionFieldEquiv K t` of $L$ with the function field of $C$ — is exactly the subring underlying the valuation subring of $P(x)$. Let $\chi \colon$ `chartRing K ({t} : Set L)` $\to K$ be a $K$-algebra homomorphism, and let $z$ be a closed point of $C$ whose underlying point is the image under $\iota_0 =$ `ι₀ K t` of the image of the closed point of $K$ under $\operatorname{Spec}(\chi)$, i.e. of the prime $\ker \chi$. Then for every $c$ in `chartRing K ({t} : Set L)` the image of $c$ in $L$ lies in the valuation subring of $P(z)$, and $c - \chi(c)$ lies in its set of nonunits, i.e. in its maximal ideal.
--
--   This is the statement that the place assigned to a $K$-rational point of the $t$-chart of the two-chart model is centred at that point, with the value of a chart function at the place computed by evaluation through $\chi$. It is used when a curve model is packaged together with a marked point, in the construction of models of modular curves and of the centring data at cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IntermediateField AlgebraicCurve AlgebraicCurve.CurveModel

universe u

theorem AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    [FiniteDimensional ↥K⟮t⟯ L]
    (P : closedPoints (glued K t) → Place K L)
    (hPst : ∀ x : closedPoints (glued K t),
      (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
        (P x).toValuationSubring.toSubring)
    (χ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K)
    (z : closedPoints (glued K t))
    (hz : z.1 = (ι₀ K t).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base
      (IsLocalRing.closedPoint K))) :
    ∀ c : ↥(chartRing K ({t} : Set L)),
      (c : L) ∈ (P z).toValuationSubring ∧
        (c : L) - algebraMap K L (χ c) ∈ (P z).toValuationSubring.nonunits := by sorry
