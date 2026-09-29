-- Prove2me | Theorems.Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
-- name    : AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/661b155a-ee86-5152-9f07-0ee06283b404
-- title:
--   Sections on U∩ V are regular at places centred in U and in V
-- statement:
--   Let $K$ be a field and let $C$ be an integral scheme over $K$, with structure morphism $c \colon C \to \operatorname{Spec} K$ assumed separated and smooth of relative dimension $1$. The ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely $K \to \Gamma(C,\mathcal O_C)$ via $c$ followed by the germ map at the generic point, makes the function field $K(C)$ a $K$-algebra, and places of $K(C)$ over $K$ are, by definition, valuation subrings $\mathcal O_v \subseteq K(C)$ that contain the image of $K$, are not all of $K(C)$, and are principal ideal rings; the associated valuation `adicValuation` is $\mathbb Z^{m0}$-valued, coming from the height-one spectrum of $\mathcal O_v$. For an open $U \subseteq C$, [`AlgebraicCurve.placesOf c U`](def/AlgebraicCurve_PlacesOf.html#L17) is the set of places $v$ for which there is a closed point $x \in U$ with $\mathcal O_v$ equal to the image of $\mathcal O_{C,x} \to K(C)$. The assertion: for opens $U, V \subseteq C$ with $U \sqcap V$ nonempty and every section $s \in \Gamma(C, U \sqcap V)$, the germ of $s$ in $K(C)$ lies in [`AlgebraicCurve.lSpaceOn`](def/AlgebraicCurve_CechSectionsOfDivisor.html#L14) of the intersection `placesOf c U` $\cap$ `placesOf c V` for the zero divisor in $\mathrm{Place}\,K\,K(C) \to_{\mathrm{f}} \mathbb Z$; concretely, $v(\text{germ}(s)) \le 1$ for every place $v$ centred at a closed point of $U$ and also at a closed point of $V$.
--
--   This is the statement that a function regular on $U \cap V$ has no pole at any place of $K(C)/K$ whose centre lies in $U$ and in $V$ — equivalently, that the cross terms of a two-chart cover land in the Riemann–Roch space $L_{S \cap T}(0)$. It is used in the comparison of Čech $H^1$ with sheaf $H^1$ for two-chart covers and in the cover-independence statements that feed the relative Picard computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
namespace AlgebraicCurve

theorem germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) [Nonempty (U ⊓ V : C.Opens)] (s : Γ(C, U ⊓ V)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (C.germToFunctionField (U ⊓ V)).hom s ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c U ∩ AlgebraicCurve.placesOf c V)
        (0 : AlgebraicCurve.Divisor K C.functionField) := by sorry
