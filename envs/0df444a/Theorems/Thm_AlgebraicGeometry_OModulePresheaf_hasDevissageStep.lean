-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep
-- name    : AlgebraicGeometry.OModulePresheaf.hasDevissageStep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/b28926c3-c24c-5c60-a20f-e12dea3a655d
-- title:
--   Existence of one dévissage step
-- statement:
--   The theorem asserts the proposition `OModulePresheaf.HasDevissageStep`, i.e. the following. Let $R$ be a Noetherian commutative ring, $V$ a Noetherian scheme and $\pi : V \to \operatorname{Spec} R$ a separated morphism. Let $F$ be a module-presheaf datum over $\pi$: an assignment of an $R$-module and a $\Gamma(V,U)$-module structure (compatibly, via the algebra structure induced by $\pi$) to each open $U \subseteq V$, together with functorial $R$-linear restriction maps semilinear over restriction of sections. Assume $F$ is coherent ($F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$) and quasi-coherent (for every affine open $U$ and $f \in \Gamma(V,U)$, every element of $F(V_f)$ becomes the restriction of a section of $F(U)$ after multiplication by some power of $f$, and every section of $F(U)$ restricting to $0$ on $V_f$ is killed by some power of $f$). Let $Y \subseteq V$ be a closed subset, nonempty, with $F$ supported in $Y$ (i.e. $F(U)$ is subsingleton whenever the affine open $U$ misses $Y$), and assume $F$ is annihilated by the ideal of $Y$: $a \cdot x = 0$ for every affine open $U$, every $a$ in the vanishing ideal of $Y$ on $U$ and every $x \in F(U)$. The conclusion is that `F.DevissageStep Y` is nonempty: there exist a nonempty closed $Z_0 \le Y$ whose vanishing-ideal subscheme is integral, a module-presheaf datum $H$ over the composite of the closed immersion $Z_0 \to V$ with $\pi$ whose pushforward $i_*H$ along that immersion is coherent, quasi-coherent and supported in $Z_0$, a datum $G_3$ over $\pi$, a term of `AffSES (pushforward π _ H) F G₃` (the project's notion of a short exact sequence with these three terms), and a closed $Z_1 < Y$ with $G_3$ coherent, quasi-coherent and supported in $Z_1$.
--
--   This is the inductive step of the dévissage of coherent modules on a Noetherian scheme, in the concrete presheaf-theoretic form used in the finiteness proof for coherent cohomology of a proper (here separated) morphism: one splits off the part of $F$ killed by the ideal of a maximal irreducible component $Z_0$ of $Y$, the quotient being supported in a strictly smaller closed subset. It is used by [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral) and [`AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral), where the induction on the support reduces statements about coherent data to the case of integral subschemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.hasDevissageStep : OModulePresheaf.HasDevissageStep.{u} := by sorry
