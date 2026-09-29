-- Prove2me | Theorems.Thm_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.IdealSheafData.flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/7d4d8bfd-895d-598a-9065-1addea7e5f4f
-- title:
--   Saturated ideal sheaves give flat closed subschemes over a DVR
-- statement:
--   Let $O$ be a discrete valuation ring (a commutative ring which is a domain and a discrete valuation ring), let $X$ be a scheme, let $q \colon X \to \operatorname{Spec} O$ be a morphism of schemes, and let $J$ be an ideal sheaf datum on $X$, i.e. a family assigning to each affine open $U \subseteq X$ an ideal $J(U) \subseteq \Gamma(X, U)$, compatible with restriction in the sense of `Scheme.IdealSheafData`. Assume the following saturation hypothesis: for every irreducible element $\varpi$ of $O$, every affine open $U$ of $X$ and every section $s \in \Gamma(X, U)$, if the product of $s$ with the restriction to $U$ of the global function $q^{*}(\varpi) \in \Gamma(X, X)$ — the image of $\varpi$ under the isomorphism $O \cong \Gamma(\operatorname{Spec} O)$ followed by $q$ on global sections — lies in $J(U)$, then already $s \in J(U)$. The conclusion is that the composite of the closed immersion $J.\mathrm{subscheme} \to X$ cut out by $J$ with $q$ is a flat morphism of schemes.
--
--   This is the standard criterion that a closed subscheme of a scheme over a discrete valuation ring is flat over the base as soon as its ideal sheaf is saturated with respect to a uniformiser, flatness over a valuation ring being equivalent to torsion-freeness. It is used in the construction of schematic closures of generic-fibre data, where the saturated ideal produces a relative effective Cartier divisor; here it feeds the existence statement [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_and_pullbackAlong_eq_and_saturated_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IdealSheafData.flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of O)) (J : X.IdealSheafData)
    (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : X.affineOpens) (s : Γ(X, U)),
        X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
            (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ J.ideal U →
          s ∈ J.ideal U) :
    Flat (J.subschemeι ≫ q) := by sorry
