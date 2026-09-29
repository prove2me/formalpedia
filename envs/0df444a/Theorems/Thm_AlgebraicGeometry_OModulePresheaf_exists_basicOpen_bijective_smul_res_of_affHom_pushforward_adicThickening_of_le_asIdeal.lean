-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal
-- name    : AlgebraicGeometry.OModulePresheaf.exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/30aabd5c-0770-59ea-b6bc-42dfeef0ddde
-- title:
--   Rank-one local freeness from invertible reductions modulo Iⁿ⁺¹
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I\subseteq R$ an ideal, $X$ a scheme and $f\colon X\to\operatorname{Spec} R$ a morphism locally of finite type. For each $n\in\mathbb N$ let $L_n$ be a module on the adic thickening `adicThickening f I n`, the fibre product of $f$ with $\operatorname{Spec}(R/I^{n+1})\to\operatorname{Spec} R$, and assume each $L_n$ is invertible in the sense that every point of that scheme has an open neighbourhood $W$ over which the pullback of $L_n$ along $W\hookrightarrow$ the thickening is isomorphic to the unit module. Let $G$ be a module presheaf over $f$: opens $U$ of $X$ are assigned modules $G(U)$ over both $R$ and $\Gamma(X,U)$, compatibly with the $R$-algebra structure on $\Gamma(X,U)$ coming from $f$, together with $R$-linear restriction maps `G.res` semilinear for restriction of scalars and functorial. Assume $G$ is coherent, i.e. $G(U)$ is a finite $\Gamma(X,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and every $s\in\Gamma(X,U)$ each element of $G(X_s)$ becomes the restriction of an element of $G(U)$ after multiplication by some power of $s$, and each element of $G(U)$ restricting to $0$ on the basic open $X_s$ is annihilated by some power of $s$. Assume given, for every $n$, a morphism $\psi_n$ on affine opens from $G$ to the pushforward along the canonical morphism `adicThickeningι f I n` of the module presheaf attached to $L_n$; that is, for each affine open $U$ an $R$-linear map $(\psi_n)_U\colon G(U)\to\Gamma(L_n,\iota_n^{-1}U)$ which is $\Gamma(X,U)$-equivariant and compatible with restriction along inclusions of affine opens. Assume further that each $(\psi_n)_U$ is surjective and that its kernel is exactly $I^{n+1}\cdot G(U)$ (as $R$-submodule, the scaling of the top submodule). Finally let $U$ be an affine open of $X$ and $x\in U$ a point whose image prime $f(x)$ contains $I$. The conclusion is the existence of $r\in\Gamma(X,U)$ and $g\in G(U)$ with $x$ in the basic open $X_r$ such that the map $\Gamma(X,X_r)\to G(X_r)$, $b\mapsto b\cdot(g|_{X_r})$, is bijective.
--
--   This is the local-algebra core of the statement that a coherent module datum whose reductions modulo all powers of $I$ are the direct images of line bundles on the $I$-adic thickenings is free of rank one on a basic open neighbourhood of each point lying over $V(I)$. It is invoked by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_affHom_pushforward_adicThickening_surjective_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_affHom_pushforward_adicThickening_surjective_ker_eq_pow_smul_top), which assembles these local trivialisations into invertibility of the module, in the development of the relative Picard functor used for Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (G : OModulePresheaf f) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom G
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : I ≤ (f.base x).asIdeal) :
    ∃ (r : Γ(X, U.1)) (g : G.obj U.1), x ∈ X.basicOpen r ∧
      Function.Bijective fun b : Γ(X, X.basicOpen r) => b • G.res (X.basicOpen_le r) g := by sorry
