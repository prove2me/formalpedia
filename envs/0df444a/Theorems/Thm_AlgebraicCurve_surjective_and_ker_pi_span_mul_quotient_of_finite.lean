-- Prove2me | Theorems.Thm_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite
-- name    : AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/677fee15-9278-5326-a2ab-8d2bd87bc7d1
-- title:
--   Local–global decomposition of a finite over-ring on a chart
-- statement:
--   Let $k$ be an algebraically closed field and let $c \colon C \to \operatorname{Spec} k$ be a morphism with $C$ an integral scheme and $c$ proper, so that $K =$ `C.functionField`, the stalk at the generic point, is a $k$-algebra via [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $k$, the map on global sections induced by $c$, and the germ map $\Gamma(C,\top) \to K$. Assume every point of $C$ is either the generic point or closed; let $U \subseteq C$ be a non-empty affine open containing the generic point, and let $B \subseteq K$ be a $\Gamma(C,U)$-subalgebra that is finite as a $\Gamma(C,U)$-module. For $z \in C$ put $B_z := \operatorname{span}_k\bigl(B \cdot \mathcal{O}_z\bigr)$, where $\mathcal{O}_z$ denotes the image of the stalk $\mathcal{O}_{C,z}$ in $K$, and let $Q_z$ be the quotient of $B_z$ by the preimage in $B_z$ of $\operatorname{span}_k \mathcal{O}_z$. Let $\varphi$ be the $k$-linear map from $\operatorname{span}_k B$ to $\prod_z Q_z$, the product taken over the closed points $z$ of $C$ lying in $U$, whose $z$-component is the inclusion $\operatorname{span}_k B \subseteq B_z$ followed by the quotient map. Then $\varphi$ is surjective, its kernel is the preimage in $\operatorname{span}_k B$ of the $k$-span of the image of $\Gamma(C,U)$ in $K$ under the germ map at the generic point, the set of closed $z \in U$ with $Q_z$ non-trivial is finite, and each $Q_z$ is a finite-dimensional $k$-vector space.
--
--   This is the local–global principle expressing the quotient of a finite over-ring $B$ of $\Gamma(C,U)$ inside the function field by $\Gamma(C,U)$ itself as the direct sum of its local contributions $B \cdot \mathcal{O}_{C,z}/\mathcal{O}_{C,z}$ at the closed points of the affine chart $U$. It is used in the comparison of $L$-spaces with their local counterparts at singular points, via [`AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen`](thm.html#AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_surjective_and_ker_pi_span_mul_quotient_of_finite.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U)
    (B : Subalgebra Γ(C, U) C.functionField) (hB : Module.Finite Γ(C, U) B) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

    let Bz : C → Submodule k C.functionField := fun z =>
      Submodule.span k ((B : Set C.functionField) * Set.range (algebraMap (C.presheaf.stalk z) C.functionField))
    let Q : C → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))).comap (Bz z).subtype

    let φ : ↥(Submodule.span k (B : Set C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)).comap
        (Submodule.span k (B : Set C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by sorry
