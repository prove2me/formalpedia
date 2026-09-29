-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective
-- name    : AlgebraicGeometry.DescentCharacter.existsUnique_isBaseScalar_of_isInvertible_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/4eb5a160-e369-5c33-aa6a-894d6a4073d0
-- title:
--   Endomorphisms of an invertible module as unique base constants
-- statement:
--   Let $X$ be a scheme, $R$ a commutative ring and $f\colon X\to\operatorname{Spec}(R)$ a morphism of schemes. Assume that the composite map $R\to\Gamma(X,\mathcal O_X)$ sending $c$ to `f.appTop` applied to the image of $c$ under the inverse of the isomorphism $R\xrightarrow{\sim}\Gamma(\operatorname{Spec}R,\mathcal O)$ is bijective. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point $x\in X$ lies in an open $U$ such that the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module (the structure sheaf) on $U$. Let $\sigma\colon M\to M$ be an endomorphism of $M$ as a sheaf of modules. Then there is exactly one $c\in R$ satisfying `IsBaseScalar f σ c`, that is, such that for every open $U\subseteq X$ and every section $s\in\Gamma(M,U)$ one has $\sigma_U(s)=(\text{res}^{\top}_{U}\,f^{\sharp}(c))\cdot s$, where $f^{\sharp}(c)\in\Gamma(X,\mathcal O_X)$ is the global function attached to $c$ as above and $\text{res}^{\top}_U$ is restriction from $X$ to $U$.
--
--   This is the statement that an $\mathcal O_X$-linear endomorphism of an invertible module is multiplication by a unique element of the base ring, once $R\to\Gamma(X,\mathcal O_X)$ is bijective (as for proper flat families with geometrically connected and reduced fibres, in particular abelian schemes). It provides the well-definedness of the value in $R$ attached to an identification of pulled-back line bundles, and is used in the construction of the torsion character and in the treatment of polarisations, via [`AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate), [`AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial`](thm.html#AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial) and [`AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.existsUnique_isBaseScalar_of_isInvertible_of_bijective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c := by sorry
