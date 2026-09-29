-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
-- name    : AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f39ae0fc-923a-59c5-9847-ac734ea726e8
-- title:
--   Connecting maps for Čech cohomology of an affine-exact sequence
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V\to\operatorname{Spec}R$ a separated morphism. Let $F_1,F_2,F_3$ be objects of `OModulePresheaf π`, i.e. data assigning to each open $U\subseteq V$ an $R$-module that is also a $\Gamma(V,U)$-module compatibly with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps semilinear over restriction of sections and functorial. Let $S$ be an `AffSES F₁ F₂ F₃`: maps $S.\mathrm{inc}\colon F_1\to F_2$ and $S.\mathrm{proj}\colon F_2\to F_3$, each given by $R$-linear maps on sections over affine opens commuting with multiplication by sections and with restriction along inclusions of affine opens, such that for every affine open $U$ the map $S.\mathrm{inc}$ is injective on $U$, $S.\mathrm{proj}$ is surjective on $U$, and the range of the former equals the kernel of the latter. Let $K$ be an `OrderedAffineCover` of $V$: a finite, linearly ordered family of affine opens covering $V$. Write $\check H^0=\ker d^0$ on the ordered Čech complex of $K$, and $\mathrm{HSucc}\ i=\ker d^{i+1}/\operatorname{im}d^i$, so that $\mathrm{HSucc}\ i$ is $\check H^{i+1}$. The assertion is that there exist $R$-linear maps $\delta^0\colon \check H^0(K,F_3)\to \check H^1(K,F_1)$ and, for every $i\in\mathbb N$, $\delta^i\colon \check H^{i+1}(K,F_3)\to \check H^{i+2}(K,F_1)$ satisfying four inclusions: $\ker\delta^0$ is contained in the range of the map $\check H^0(K,F_2)\to\check H^0(K,F_3)$ induced by $S.\mathrm{proj}$; for every $i$, $\ker\delta^i$ is contained in the range of the induced map $\check H^{i+1}(K,F_2)\to\check H^{i+1}(K,F_3)$; the kernel of the map $\check H^1(K,F_1)\to\check H^1(K,F_2)$ induced by $S.\mathrm{inc}$ is contained in the range of $\delta^0$; and for every $i$, the kernel of $\check H^{i+2}(K,F_1)\to\check H^{i+2}(K,F_2)$ is contained in the range of $\delta^i$. Only these inclusions are asserted, not the reverse ones, nor exactness at $\check H^\bullet(K,F_2)$, nor any uniqueness or naturality of the $\delta$'s.
--
--   This is the connecting-homomorphism half of the long exact Čech cohomology sequence attached to a sequence of $\mathcal O_V$-module presheaf data that is exact on affine opens, obtained by the snake lemma from the degreewise exact sequence of ordered Čech complexes; the statement is phrased as an existence so that no named connecting map is introduced. It is used in the injectivity criterion [`AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map`](thm.html#AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map) and in the finiteness transfer results [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left) and [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) : ∃ (δ₀ : F₃.H0 K →ₗ[R] F₁.HSucc K 0) (δ : ∀ i : ℕ, F₃.HSucc K i →ₗ[R] F₁.HSucc K (i + 1)), LinearMap.ker δ₀ ≤ LinearMap.range (S.proj.H0Map K) ∧ (∀ i, LinearMap.ker (δ i) ≤ LinearMap.range (S.proj.HSuccMap K i)) ∧ LinearMap.ker (S.inc.HSuccMap K 0) ≤ LinearMap.range δ₀ ∧ (∀ i, LinearMap.ker (S.inc.HSuccMap K (i + 1)) ≤ LinearMap.range (δ i)) := by sorry
