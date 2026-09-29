-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.isLocalizedModule_res_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4409480a-10d6-57eb-8040-c7db26849e59
-- title:
--   Quasi-coherence makes restriction to a basic open a localisation
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a morphism, and let $F$ be an `OModulePresheaf` over $\pi$: a datum assigning to each open $U\subseteq V$ an abelian group $F.obj\,U$ carrying an $R$-module structure and a $\Gamma(V,U)$-module structure compatible over $R$ (via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$), together with $R$-linear restriction maps $F.res$ for inclusions $U\le U'$ that are semilinear for the restriction homomorphism $\Gamma(V,U')\to\Gamma(V,U)$ and satisfy the identity and composition laws. Assume $F$ satisfies `IsQuasicoherent`, i.e. for every affine open $U$ of $V$ and every $f\in\Gamma(V,U)$: (i) each $x\in F.obj\,(V.basicOpen\,f)$ can be written as $F.res\,y = (f^n|_{D(f)})\cdot x$ for some $n\in\mathbb N$ and $y\in F.obj\,U$, and (ii) each $y\in F.obj\,U$ with $F.res\,y=0$ is killed by some power $f^n$. Then, for any affine open $U$ of $V$ and any $f\in\Gamma(V,U)$, when $F.obj\,(V.basicOpen\,f)$ is viewed as a $\Gamma(V,U)$-module through the restriction homomorphism (`F.moduleRestrict`), the $\Gamma(V,U)$-linear restriction map `F.resₗ (V.basicOpen_le f)` from $F.obj\,U$ to $F.obj\,(V.basicOpen\,f)$ exhibits the latter as the localisation of the former at the submonoid of powers of $f$.
--
--   This is the standard local description of a quasi-coherent module: sections over a basic open $D(f)$ inside an affine open $U$ form the localisation $F(U)_f$. It is the bridge from the project's axiomatic quasi-coherence datum to Mathlib's `IsLocalizedModule` API, and is used downstream in the statements comparing $F$ with tensor products and in the finiteness and coherence arguments for such module data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Mathlib.Algebra.Module.LocalizedModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.isLocalizedModule_res_of_isQuasicoherent
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (hq : F.IsQuasicoherent) (U : V.affineOpens) (f : Γ(V, U.1)) :
    letI := F.moduleRestrict (V.basicOpen_le f)
    IsLocalizedModule (Submonoid.powers f) (F.resₗ (V.basicOpen_le f)) := by sorry
