-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/7bf7366e-3ed4-5960-a4f7-0a94b55581ff
-- title:
--   Vanishing of Čech H¹ is independent of the ordered affine cover
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\pi \colon X \to \operatorname{Spec} R$ a separated morphism, and let $M$ be a sheaf of $\mathcal{O}_X$-modules on $X$. Assume $M$ is locally free of rank one in the strong sense that every point $x$ of $X$ lies in an open $W$ for which the pullback of $M$ along the inclusion $W \hookrightarrow X$ is isomorphic to the unit module $\mathcal{O}_W$ of the sheaf of rings of $W$ (the isomorphism being asserted only to exist, as a `Nonempty` hypothesis). Let $K$ and $K'$ be two ordered affine covers of $X$ in the sense of `Scheme.OrderedAffineCover`: each consists of a finite linearly ordered index type together with a family of affine open subsets of $X$ whose supremum is $\top$. Write $F =$ `OModulePresheaf.ofModules π M` for the presheaf $U \mapsto \Gamma(M, U)$ equipped with its $R$-module structure coming from $\pi$, its $\Gamma(X,U)$-module structure, and the restriction maps of $M$. Then if the first cohomology $\ker (d_K^1) / \operatorname{im}(d_K^0)$ of the Čech complex of $F$ with respect to $K$ — in the Lean formulation, the quotient of $\ker(F.d\,K\,1)$ by the preimage in it of the range of $F.d\,K\,0$, i.e. `F.HSucc K 0` — is a subsingleton, the corresponding quotient `F.HSucc K' 0` for the cover $K'$ is a subsingleton as well.
--
--   This is the cover-independence of the vanishing of first Čech cohomology for a locally trivial module on a separated scheme, the computational substitute here for the identification of Čech cohomology with respect to an affine cover with sheaf cohomology. It is used in the treatment of $H^1$ of tensor powers of an invertible module on a proper smooth curve, and in the construction of sections of such powers with prescribed behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (K K' : X.OrderedAffineCover) (h : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K 0)) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc K' 0) := by sorry
