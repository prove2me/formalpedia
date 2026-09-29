-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
-- name    : AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/b45d37e1-8ed3-54ac-9d48-97b704850d29
-- title:
--   Vanishing-ideal powers eventually annihilate a coherent datum supported in Y
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme with a morphism $\pi\colon V\to\operatorname{Spec} R$, and assume $V$ is locally Noetherian. Let $Y$ be a closed subset of the underlying space of $V$, and let $F$ be an `OModulePresheaf` for $\pi$: a rule assigning to each open $U\subseteq V$ an abelian group $F(U)$ carrying an $R$-module structure and a $\Gamma(V,U)$-module structure, compatible as a scalar tower over the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F(U')\to F(U)$ for $U\le U'$ which are semilinear for restriction of ring sections, reflexive and transitive. Three hypotheses are imposed. Coherence: $F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$. Quasi-coherence: for every affine open $U$ and every $f\in\Gamma(V,U)$, each element of $F(V_f)$ becomes, after multiplication by some power of $f$, the restriction of an element of $F(U)$, and each element of $F(U)$ restricting to $0$ on the basic open $V_f$ is killed by some power of $f$. Support in $Y$: $F(U)$ is a subsingleton for every affine open $U$ with $U\cap Y=\emptyset$. The conclusion, for a fixed affine open $U$ of $V$, is that there exists $N\in\mathbb{N}$ such that $\mathrm{idealPowSub}$ at stage $N$ vanishes, i.e. the $\Gamma(V,U)$-submodule $I(U)^N\cdot F(U)=\top$ of $F(U)$, viewed as an $R$-submodule by restriction of scalars, is $\bot$, where $I(U)$ is the kernel of the map $\Gamma(V,U)\to\Gamma$ of the closed subscheme inclusion attached to the vanishing ideal sheaf data of $Y$.
--
--   This is the termination statement for the $I_Y$-adic filtration $F\supseteq I_YF\supseteq I_Y^2F\supseteq\cdots$ on a fixed affine open: a coherent, quasi-coherent datum supported in the closed set $Y$ is annihilated by a sufficiently high power of the vanishing ideal of $Y$. It feeds the dévissage of the finiteness theorem for Čech cohomology of coherent data, being used by [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot) and by [`AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates), which reduce assertions about $F$ to assertions about the graded pieces $I_Y^kF/I_Y^{k+1}F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (U : V.affineOpens) : ∃ N : ℕ, OModulePresheaf.idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ := by sorry
