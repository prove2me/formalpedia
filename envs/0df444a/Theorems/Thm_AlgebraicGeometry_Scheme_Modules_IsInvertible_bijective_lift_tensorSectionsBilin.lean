-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/0178347b-8344-59ff-bca0-464c3d5ff93e
-- title:
--   Sections of a tensor product of invertible sheaves on an affine open
-- statement:
--   Let $X$ be a scheme and let $L$ and $M$ be sheaves of modules over the structure sheaf of $X$, each assumed invertible in the sense that every point of $X$ lies in an open $U$ for which the pullback of the sheaf along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $U$ be an affine open of $X$, and write $A = \Gamma(X, U)$ for the ring of sections of the structure sheaf on $U$. The bilinear map `tensorSectionsBilin` sends a pair $(s,t) \in \Gamma(L,U) \times \Gamma(M,U)$ to the section `tensorSections s t` of $L \otimes M$ over $U$, namely the image of $s \otimes_A t$ under the component at $U$ of the canonical map `tensorSectionsHom` from the pointwise tensor product of the underlying presheaves of modules to the monoidal tensor product $L \otimes M$; it is $A$-linear in each argument. The assertion is that the induced $A$-linear map
--   $$\Gamma(L,U) \otimes_A \Gamma(M,U) \longrightarrow \Gamma(L \otimes M, U)$$
--   obtained from this bilinear map is bijective, hence an isomorphism of $A$-modules.
--
--   This is the affine-open case of the identification of the sections of a tensor product of quasi-coherent sheaves, specialised to line bundles: over an affine open the tensor product of sheaves of modules computes the tensor product of section modules. It is used in computing Euler characteristics of successive twists, being cited by [`AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq) and its variant for opens not contained in the support of the relevant ideal, where the twist by $L^{\otimes(n+1)}$ over an affine open must be related to the twists by $L^{\otimes n}$ and by $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) := by sorry
