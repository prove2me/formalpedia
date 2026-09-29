-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/a82985b2-60ca-56bb-a0ea-9568deeb89a0
-- title:
--   Coherence of the graded pieces I^kF/I^{k+1}F
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V \to \operatorname{Spec} R$ a morphism of schemes, with $V$ locally Noetherian. Let $I$ be an ideal sheaf datum on $V$, let $F$ be an `OModulePresheaf` for $\pi$ — that is, an assignment of an $R$-module $F(U)$ to each open $U \subseteq V$, carrying in addition a $\Gamma(V,U)$-module structure compatible with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for the restriction of sections and satisfy the presheaf identities — and let $k$ be a natural number. Assume $F$ is coherent in the sense of `IsCoherent`: for every affine open $U$ of $V$, $F(U)$ is a finite $\Gamma(V,U)$-module. The conclusion is that the presheaf `idealPowQuot π I F k` is coherent in the same sense; by construction its value on an open $U$ is the quotient of the submodule $I(U)^k \cdot F(U)$ of $F(U)$ by the submodule $I(U)^{k+1} \cdot F(U)$ sitting inside it, so the assertion is that for every affine open $U$ the $\Gamma(V,U)$-module $I(U)^kF(U)/I(U)^{k+1}F(U)$ is finite.
--
--   This is the coherence of the graded pieces of the $I$-adic filtration $F \supseteq IF \supseteq I^2F \supseteq \cdots$, formed open by open on module-presheaf data. It is used in the finiteness argument for Čech cohomology of coherent data, where a datum supported in a closed subscheme is reduced to data annihilated by the corresponding ideal sheaf; it is cited by [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral), [`AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top) and [`AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFc : F.IsCoherent) : (OModulePresheaf.idealPowQuot π I F k).IsCoherent := by sorry
