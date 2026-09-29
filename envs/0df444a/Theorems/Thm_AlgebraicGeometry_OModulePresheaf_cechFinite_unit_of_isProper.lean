-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/16a7d432-fe80-56b1-88b3-930a1bc71b5a
-- title:
--   Čech finiteness of the structure sheaf of a proper scheme
-- statement:
--   Let $R$ be a Noetherian commutative ring (in universe $u$), let $V$ be a scheme and let $\pi \colon V \to \operatorname{Spec} R$ be a proper morphism. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$, each affine, whose supremum is all of $V$. Consider the $\mathcal O$-module presheaf `OModulePresheaf.unit π`, the structure sheaf viewed in the project's sense: it assigns to an open $U$ the ring $\Gamma(V, U)$, with its $\Gamma(V,U)$-module structure by multiplication and its $R$-module structure obtained from $\pi$ (through the algebra map $R \to \Gamma(V,U)$ induced by $\pi$ on global sections followed by restriction), and with restriction along $U \le U'$ given by the presheaf restriction map $\Gamma(V,U') \to \Gamma(V,U)$, which is $R$-linear and multiplicative. The conclusion is `CechFinite K` for this presheaf: the degree-zero module $H^0$ of the Čech complex attached to $K$ is a finite $R$-module, and for every $i$ the module $\ker(d_{i+1})/\operatorname{im}(d_i)$ is a finite $R$-module as well. Thus all Čech cohomology modules of $\mathcal O_V$ with respect to $K$ are finitely generated over $R$.
--
--   This is the case $F = \mathcal O_V$ of the finiteness theorem for coherent cohomology of a proper morphism over a Noetherian base, in the Čech form used in this development. It feeds the finiteness of $\Gamma(V, \mathcal O_V)$ as an $R$-module ([`AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing`](thm.html#AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing)), the finiteness of $H^0$ and $H^1$ for a two-chart cover ([`AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_structureSheaf`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_structureSheaf)), and the rank computations for the fake elliptic curves of the Čerednik–Drinfeld part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover) : (OModulePresheaf.unit π).CechFinite K := by sorry
