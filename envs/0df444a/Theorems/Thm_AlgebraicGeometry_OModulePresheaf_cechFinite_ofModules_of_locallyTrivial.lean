-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/c9890c3c-f4cc-5071-8dc1-acc053e26321
-- title:
--   Finiteness of Čech cohomology of locally trivial 𝒪-modules
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $V$ be a scheme and let $\pi\colon V\to\operatorname{Spec} R$ be a proper morphism. Let $M$ be a sheaf of $\mathcal O_V$-modules, and assume $M$ is Zariski-locally trivial in the following sense: every point $x$ of $V$ lies in some open $U\subseteq V$ for which the pullback of $M$ along the inclusion $U\hookrightarrow V$ is isomorphic, as a sheaf of modules on $U$, to the structure sheaf of $U$ viewed as a module over itself. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ together with opens $U_i\subseteq V$, each affine, with $\bigsqcup_i U_i=\top$. The conclusion is that the datum $U\mapsto\Gamma(M,U)$, with its $R$-module structure obtained from the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$ and with the $R$-linear restriction maps of $M$, has finite Čech cohomology with respect to $K$: the degree-zero module of the associated alternating Čech complex is a finite $R$-module, and so is, for every $i$, the quotient of $\ker(d_{i+1})$ by the image of $d_i$.
--
--   This is the finiteness theorem for the cohomology of coherent sheaves on a proper scheme over a Noetherian ring (EGA III 3.2.1; Hartshorne III.5.2 in the projective case), specialised to sheaves that are locally isomorphic to the structure sheaf, such as invertible sheaves, and phrased for the Čech complex of a prescribed finite affine open cover. It feeds the computations of Euler characteristics and of Čech ranks under base change used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) : (OModulePresheaf.ofModules π M).CechFinite K := by sorry
