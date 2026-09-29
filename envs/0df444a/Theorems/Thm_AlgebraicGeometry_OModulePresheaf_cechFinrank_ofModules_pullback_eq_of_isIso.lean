-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/74e454d0-b4d6-5c9d-8236-5b56c9186760
-- title:
--   Čech ranks of an invertible module are invariant under isomorphism
-- statement:
--   Let $R$ be a commutative ring, let $P$ and $P'$ be schemes, let $\pi' \colon P' \to \operatorname{Spec} R$ be separated, and let $\Phi \colon P \to P'$ be an isomorphism of schemes. Let $N$ be a module over the structure sheaf of $P'$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of $P'$ has an open neighbourhood $U$ such that the pullback of $N$ along the inclusion $U \hookrightarrow P'$ is isomorphic to the unit sheaf of modules on $U$. Let $\mathfrak{W}$ and $\mathfrak{W}'$ be ordered affine covers of $P$ and of $P'$ respectively, that is, finite linearly ordered families of affine opens whose supremum is the whole scheme, and let $n$ be a natural number. Then the $n$-th Čech rank over $R$ of the presheaf of $R$-modules $U \mapsto \Gamma(\Phi^{*}N, U)$ associated with the structure morphism $\Phi$ followed by $\pi'$, computed with respect to $\mathfrak{W}$, equals the $n$-th Čech rank over $R$ of $U \mapsto \Gamma(N, U)$ over $\pi'$, computed with respect to $\mathfrak{W}'$. Here the $n$-th Čech rank is `Module.finrank` over $R$ of the Čech $H^0$ of the cover when $n = 0$, and of the $i$-th higher Čech cohomology group $\ker d_{i+1} / \operatorname{im} d_i$ when $n = i+1$; $R$-module structures on sections come from the algebra structure induced by the structure morphism.
--
--   This is the combination of two standard facts for an invertible (hence quasi-coherent) module on a separated scheme: independence of Čech cohomology of the chosen finite affine cover, and invariance of cohomology under pullback along an isomorphism of schemes. It is used in the computations of Čech ranks and Euler characteristics of line bundles, for instance in the results on ranks of twists by pullbacks and on the behaviour of the Euler characteristic under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated π']
    (Φ : P ⟶ P') [IsIso Φ]
    (N : P'.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝔚 : P.OrderedAffineCover) (𝔚' : P'.OrderedAffineCover) (n : ℕ) :
    (OModulePresheaf.ofModules (Φ ≫ π') ((Scheme.Modules.pullback Φ).obj N)).cechFinrank 𝔚 n =
      (OModulePresheaf.ofModules π' N).cechFinrank 𝔚' n := by sorry
