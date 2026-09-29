-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_coker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/87d27314-91b9-55a7-a016-c41af7984b2a
-- title:
--   Quasi-coherence passes to cokernels of presheaf module maps
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V\to\operatorname{Spec}R$ a morphism; let $F,G$ be module-presheaf data over $\pi$ in the sense of `OModulePresheaf`, that is, an assignment of an $R$-module and a $\Gamma(V,U)$-module structure (compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$) to each open $U\subseteq V$, together with $R$-linear restriction maps along inclusions that are semilinear for restriction of sections and satisfy the identity and composition laws. Let $\varphi\colon F\to G$ be a `Hom`, i.e. a family of $R$-linear maps $\varphi_U\colon F(U)\to G(U)$ commuting with the $\Gamma(V,U)$-actions and with restriction. Assume $G$ and $F$ both satisfy `IsQuasicoherent`: for every affine open $U$ and every $f\in\Gamma(V,U)$, every element of the module at the basic open $V_f$ becomes, after multiplication by the restriction of some power $f^n$, the restriction of an element from $U$; and every element of the module at $U$ restricting to $0$ on $V_f$ is annihilated by some power $f^n$. Then the open-by-open cokernel `coker φ`, whose value on $U$ is $G(U)/\operatorname{range}(\varphi_U)$ with the induced actions and restrictions, again satisfies `IsQuasicoherent`.
--
--   This is the elementwise, affine-local formulation of the statement that quasi-coherent modules are stable under cokernels, phrased for presheaf-level module data over a scheme mapping to $\operatorname{Spec}R$. It is one of the closure properties used in the Čech-theoretic finiteness arguments of the project, and is invoked in the construction of the short exact sequences of `Leray.exists_chowSES` and in the properness-based statement `exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_coker {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsQuasicoherent) (hF : F.IsQuasicoherent) : (OModulePresheaf.coker φ).IsQuasicoherent := by sorry
