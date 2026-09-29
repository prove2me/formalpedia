-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
-- name    : AlgebraicGeometry.SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/3348205b-0c80-5bf1-a3b3-64ebcd98018e
-- title:
--   Sections through regular points lie in the smooth locus
-- statement:
--   Let $A$ be a commutative ring which is a domain and a discrete valuation ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} A$ be a morphism which is flat and locally of finite presentation. Let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c`, that is, a pair consisting of a morphism $\varepsilon_1 \colon \operatorname{Spec} A \to C$ together with a proof that $\varepsilon_1$ followed by $c$ is the identity of $\operatorname{Spec} A$; in other words $\varepsilon$ is a section of $c$. Write $x_0 = \varepsilon_1(\mathfrak m_A)$ for the image under the underlying continuous map of $\varepsilon_1$ of the closed point of the local ring $A$. Assume that the stalk $\mathcal O_{C,x_0}$ is a regular local ring. Then $x_0$ belongs to the smooth locus of $c$, i.e. $x_0 \in$ `c.smoothLocus`.
--
--   This is the pointwise form of the statement that a section of a flat, locally finitely presented scheme over a discrete valuation ring meets the smooth locus at every point where the local ring is regular (Bosch–Lütkebohmert–Raynaud, Néron Models, §3.1, Proposition 2). It is used in the Néron model infrastructure, in particular by [`AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal`](thm.html#AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal), to pass from regularity of a model along a section to smoothness on a neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.apply_closedPoint_mem_smoothLocus_of_isRegularLocalRing_stalk
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation c] [Flat c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (hreg : IsRegularLocalRing (C.presheaf.stalk (ε.1.base (IsLocalRing.closedPoint A)))) :
    ε.1.base (IsLocalRing.closedPoint A) ∈ c.smoothLocus := by sorry
