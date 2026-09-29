-- Prove2me | Theorems.Thm_AlgebraicGeometry_eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- name    : AlgebraicGeometry.eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/a35f8c07-0082-5631-ad70-57416097be61
-- title:
--   Euler characteristic bound for a reduced curve with two branches
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a reduced scheme and let $x \colon X \to \operatorname{Spec} k$ be proper. Let $F_1,F_2$ be fields equipped with $k$-algebra structures, and let $M_1,M_2$ be curve models of $F_1,F_2$ over $k$: each consists of an integral scheme $M_i.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$ via $M_i.\mathrm{toBase}$, together with a ring isomorphism of $F_i$ with the function field of $M_i.C$ compatible with the two maps from $k$, a bijection from the closed points of $M_i.C$ to the places of $F_i$ over $k$ identifying each stalk with the corresponding valuation subring, and the property that every finite set of points of $M_i.C$ lies in an affine open. Let $\nu_i \colon M_i.C \to X$ be morphisms with $\nu_i$ followed by $x$ equal to $M_i.\mathrm{toBase}$, such that the union of the ranges of the underlying maps of $\nu_1,\nu_2$ is all of $X$, their intersection is finite, and the stalk map of $\nu_i$ at the generic point of $M_i.C$ is an isomorphism. Let $\mathcal{V}$ be a two-chart affine open cover of $X$, i.e. affine opens $U_0,U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Write $H^0$ for the kernel and $H^1$ for the cokernel of the Čech difference map $\Gamma(X,U_0) \times \Gamma(X,U_1) \to \Gamma(X,U_0 \sqcap U_1)$ attached to the structure sheaf of $X$ viewed as a module over itself, both regarded as $k$-vector spaces through $x$. Then $$\dim_k H^0 - \dim_k H^1 \le (1 - g(F_1)) + (1 - g(F_2)) - \#\{z \in X : \mathcal{O}_{X,z} \text{ is not a regular local ring}\},$$ where $g(F_i) = \operatorname{genusFF} k F_i$ is the $k$-dimension of the quotient of the algebra of repartitions of $F_i$ by the sum of the repartitions bounded by the zero divisor and the principal repartitions, and the final cardinality is the `Nat.card` of the set of non-regular points, hence $0$ should that set be infinite.
--
--   This is the $\delta$-invariant form of the genus inequality for a reduced proper curve over an algebraically closed field having two branches with function fields $F_1$ and $F_2$: the Euler characteristic of the structure sheaf, computed from a two-chart Čech complex, is bounded by the sum of the contributions $1-g(F_i)$ of the two smooth models minus the number of singular points. It combines the irreducible case with the gluing estimate for two closed subcurves, and is used in the analysis of the non-regular points of the fibres of the two-chart integral model of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] [IsReduced X]
    {F₁ F₂ : Type v} [Field F₁] [Algebra k F₁] [Field F₂] [Algebra k F₂]
    (M₁ : AlgebraicCurve.CurveModel k F₁) (M₂ : AlgebraicCurve.CurveModel k F₂)
    (ν₁ : M₁.C ⟶ X) (ν₂ : M₂.C ⟶ X) (hν₁ : ν₁ ≫ x = M₁.toBase) (hν₂ : ν₂ ≫ x = M₂.toBase)
    (hcover : Set.range ν₁.base ∪ Set.range ν₂.base = Set.univ)
    (hfin : (Set.range ν₁.base ∩ Set.range ν₂.base).Finite)
    (hbir₁ : IsIso (ν₁.stalkMap (genericPoint M₁.C)))
    (hbir₂ : IsIso (ν₂.stalkMap (genericPoint M₂.C)))
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 ≤
      (1 - (AlgebraicCurve.genusFF k F₁ : ℤ)) + (1 - (AlgebraicCurve.genusFF k F₂ : ℤ)) -
        (Nat.card {z : X // ¬ IsRegularLocalRing (X.presheaf.stalk z)} : ℤ) := by sorry
