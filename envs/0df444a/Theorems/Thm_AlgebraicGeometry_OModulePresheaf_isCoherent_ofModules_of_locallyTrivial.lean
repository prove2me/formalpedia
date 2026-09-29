-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/fa27375e-f278-5672-8271-2791d593270e
-- title:
--   Locally trivial mathcal O_V-modules are coherent on affine opens
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme, let $\pi\colon V\to\operatorname{Spec}R$ be a morphism of schemes, and let $M$ be a sheaf of modules over the structure sheaf of $V$. Assume $M$ is Zariski-locally trivial in the following sense: for every point $x$ of $V$ there is an open $U\subseteq V$ with $x\in U$ such that the pullback of $M$ along the inclusion $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules on $U$, i.e. to the structure sheaf of $U$ viewed as a module over itself (the isomorphism is asserted only to exist). The conclusion is that the $\mathcal O$-module presheaf datum `OModulePresheaf.ofModules π M` — whose value on an open $U$ is $\Gamma(M,U)$, with its $\Gamma(V,U)$-module structure, its $R$-module structure obtained from $\pi$ through the algebra map $R\to\Gamma(V,U)$, and restriction given by the maps of $M$ — satisfies the predicate `IsCoherent`, which by definition says: for every affine open $U$ of $V$, the module of sections $\Gamma(M,U)$ is a finite $\Gamma(V,U)$-module. Thus $\pi$ enters only through the $R$-linear structure carried by the datum, not through the finiteness assertion itself.
--
--   This is the standard passage from local triviality of an $\mathcal O_V$-module (an invertible sheaf, or a locally free sheaf trivialised on a cover) to coherence in the affine-local form used by the Čech vocabulary of this development: finite generation over every affine open, not merely over the members of some cover. It is the entry point for the Čech-finiteness and Euler-characteristic computations built on `OModulePresheaf`, notably [`AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    (OModulePresheaf.ofModules π M).IsCoherent := by sorry
