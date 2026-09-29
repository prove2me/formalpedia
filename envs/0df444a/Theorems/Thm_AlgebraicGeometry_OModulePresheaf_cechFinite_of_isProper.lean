-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/5490c1c3-1ba3-5145-83f8-910f90828547
-- title:
--   Finiteness of Čech cohomology for proper morphisms
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme and $\pi \colon V \to \operatorname{Spec} R$ a proper morphism. Let $F$ be an `OModulePresheaf` over $\pi$: an assignment of an $R$-module $F(U)$ to each open $U \subseteq V$, each also a $\Gamma(V,U)$-module compatibly with the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restrictions $F(U') \to F(U)$ for $U \le U'$ that are semilinear over the restriction $\Gamma(V,U') \to \Gamma(V,U)$ and are functorial (identity on $U \le U$, compatible with composition). Assume $F$ is coherent, i.e. $F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and $f \in \Gamma(V,U)$ every $x \in F(D(f))$ satisfies $f^n x = \mathrm{res}(y)$ for some $n$ and some $y \in F(U)$, and every $y \in F(U)$ restricting to $0$ in $F(D(f))$ is killed by some $f^n$. Let $K$ be an ordered affine cover of $V$: a finite, linearly ordered family of affine opens $U_i$ with $\bigsqcup_i U_i = \top$. Then $F$ satisfies `CechFinite K`: the module $H^0$ of the alternating Čech complex of $F$ on $K$ is a finite $R$-module, and so is each $\ker(d_{i+1})/\operatorname{im}(d_i)$.
--
--   This is Grothendieck's finiteness theorem for the cohomology of a coherent sheaf under a proper morphism over a Noetherian base (EGA III 3.2.1), stated for module-presheaf data and in terms of the alternating Čech complex of a fixed finite ordered affine cover. It is the source of all finiteness statements used downstream, being invoked for the structure presheaf itself and in the treatment of Euler characteristics and of locally trivial modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsProper π]
    (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) (K : V.OrderedAffineCover) :
    F.CechFinite K := by sorry
