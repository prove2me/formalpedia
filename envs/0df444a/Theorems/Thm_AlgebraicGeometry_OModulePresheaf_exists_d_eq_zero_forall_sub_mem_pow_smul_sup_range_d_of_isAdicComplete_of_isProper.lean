-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/7edf223f-ac2f-5187-a204-08ab6637a161
-- title:
--   Lifting compatible Čech classes in positive degree over a complete base
-- statement:
--   Let $A$ be a Noetherian commutative ring and $I \subseteq A$ an ideal for which $A$ is $I$-adically complete and separated, let $P$ be a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism, and let $F$ be an `OModulePresheaf` over $q$: an assignment to each open $U \subseteq P$ of an $A$-module $F.obj\,U$ carrying also a $\Gamma(P,U)$-module structure compatible with the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restriction maps $F.res : F.obj\,U' \to F.obj\,U$ for $U \le U'$ that are semilinear for the presheaf restriction of $\Gamma$, are the identity for $U = U'$, and compose. Assume `F.IsCoherent`, i.e. $F.obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `F.IsQuasicoherent`, i.e. for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index type with affine opens whose supremum is $\top$; write $C^j = F.cochain\,K\,j$ for the product of the modules $F.obj$ over the intersections indexed by $K.Idx\,j$, and $F.d\,K\,j : C^j \to C^{j+1}$ for the Čech differential. Fix $i \in \mathbb{N}$ and a family $t_n \in C^{i+1}$, $n \in \mathbb{N}$, such that $F.d\,K\,(i+1)\,(t_n) \in I^{n+1} C^{i+2}$ and $t_{n+1} - t_n \in I^{n+1} C^{i+1} + \operatorname{range}(F.d\,K\,i)$ for all $n$. Then there exists $a \in C^{i+1}$ with $F.d\,K\,(i+1)\,a = 0$ and $a - t_n \in I^{n+1} C^{i+1} + \operatorname{range}(F.d\,K\,i)$ for every $n$.
--
--   This is the existence (surjectivity) half of the theorem on formal functions in positive Čech degree: a system of classes in $\check H^{i+1}$ of the truncations, compatible modulo $I^{n+1}$ and modulo coboundaries, is realised by a genuine $(i+1)$-cocycle on $P$. It is used by the companion statement [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper), and rests on the approximate-cocycle and Artin–Rees style results `exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper` and `exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper` together with the finiteness `cechFinite_of_isProper`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈
      I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i) := by sorry
