-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/be5d2240-e029-50b0-9165-617f10dc28fc
-- title:
--   Quasi-coherence of the graded pieces I^kF/I^{k+1}F
-- statement:
--   Fix a commutative ring $R$, a scheme $V$, a morphism $\pi\colon V \to \operatorname{Spec} R$, ideal sheaf data $I$ on $V$, and a module-presheaf datum $F$ over $\pi$, that is, an assignment of an $R$-module and a $\Gamma(V,U)$-module structure, compatible via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, to each open $U \subseteq V$, together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for the restriction maps of the structure sheaf and are functorial. Let $k \in \mathbb N$, and assume $F$ is quasi-coherent in the sense that for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$: every $x \in F(V.\mathrm{basicOpen}\, f)$ satisfies $F.\mathrm{res}\, y = f^n|_{V.\mathrm{basicOpen}\, f} \cdot x$ for some $n$ and some $y \in F(U)$, and every $y \in F(U)$ restricting to $0$ on $V.\mathrm{basicOpen}\, f$ is annihilated by some power $f^n$. The conclusion is that the datum `idealPowQuot π I F k`, whose value on $U$ is the quotient of the $R$-submodule underlying $I(U)^k \cdot F(U)$ by the preimage in it of $I(U)^{k+1} \cdot F(U)$, with the induced $\Gamma(V,U)$-action and the restrictions induced by those of $F$, satisfies the same quasi-coherence condition.
--
--   This is the statement that the graded pieces $\mathcal I^kF/\mathcal I^{k+1}F$ of the $\mathcal I$-adic filtration of a quasi-coherent module-presheaf datum are again quasi-coherent. It feeds the dévissage by which finiteness statements for a datum supported in a closed subscheme are reduced to data annihilated by the corresponding ideal sheaf, and is used by [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral), [`AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top) and [`AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFq : F.IsQuasicoherent) : (OModulePresheaf.idealPowQuot π I F k).IsQuasicoherent := by sorry
