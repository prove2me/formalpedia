-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_tensorUnit_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/7a59b955-b2d0-5146-9d7d-83a5e7693b11
-- title:
--   Čech cohomology of the unit mathcal O_V-module versus mathcal O_V
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme and let $\pi \colon V \to \operatorname{Spec}(R)$ be a separated morphism. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type together with affine opens $U_i \subseteq V$ whose supremum is $\top$. Two data of $R$-linear sections on the opens of $V$ are compared: `OModulePresheaf.ofModules π (𝟙_ (V.Modules))`, whose value on $U$ is the group of sections over $U$ of the monoidal unit of the category of $\mathcal O_V$-modules, with $R$-action induced along $\pi$ through $\Gamma(V,U)$ and restriction maps those of the module; and `OModulePresheaf.unit π`, whose value on $U$ is $\Gamma(V,U)$ itself, viewed as an $R$-algebra via $\pi$, with the restriction ring homomorphisms. The assertion is that the associated Čech objects for the cover $K$ are $R$-linearly isomorphic: there exists an $R$-linear isomorphism between the kernels of the degree-$0$ Čech differentials, and for every natural number $i$ there exists an $R$-linear isomorphism between the quotients $\ker d^{i+1} / \operatorname{im} d^{i}$ of the two Čech complexes. Both conclusions are stated as nonemptiness of the type of such isomorphisms, so no particular isomorphism is singled out.
--
--   This is a compatibility statement between the two spellings of the structure sheaf occurring on this site: the sections of the tensor unit of the monoidal category of $\mathcal O_V$-modules, and the presheaf of $R$-algebras $U \mapsto \Gamma(V,U)$ used for Čech computations. It lets results proved for one datum be transported to the other, and is used in the polarisation computations, for instance in identifying $H^0$ of the structure sheaf of an abelian variety and in the vanishing statements for line bundles in the identity component of the Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_tensorUnit_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_tensorUnit_unit
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π (𝟙_ (V.Modules))).H0 K ≃ₗ[R] (OModulePresheaf.unit π).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π (𝟙_ (V.Modules))).HSucc K i ≃ₗ[R] (OModulePresheaf.unit π).HSucc K i) := by sorry
