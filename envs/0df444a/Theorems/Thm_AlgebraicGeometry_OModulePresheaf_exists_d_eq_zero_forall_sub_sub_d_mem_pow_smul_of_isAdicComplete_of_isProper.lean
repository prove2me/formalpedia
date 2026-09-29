-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/47f594d7-4696-51ca-b205-b40940f916ad
-- title:
--   Formal Čech cochains: cocycle plus formal coboundary
-- statement:
--   Let $A$ be a Noetherian commutative ring and $I \subseteq A$ an ideal for which $A$ is $I$-adically complete and separated, let $P$ be a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. Let $F$ be an $\mathcal O$-module presheaf over $q$, that is, an assignment to every open $U \subseteq P$ of an $A$-module and $\Gamma(P,U)$-module $F.obj\,U$ (the two actions compatible via the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$), together with $A$-linear restriction maps for $U \le U'$ that are semilinear over the restriction maps of the structure presheaf and satisfy the usual reflexivity and composition identities. Assume $F$ is coherent, i.e. $F.obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index type together with affine opens whose supremum is $\top$; write $C^i = F.cochain\,K\,i$ for the module of families of sections of $F$ over the intersections $\bigcap_j K.U(s_j)$ indexed by the $i$-indices of $K$, with Čech differentials $d^i : C^i \to C^{i+1}$. Fix $i \in \mathbb N$ and a sequence $t : \mathbb N \to C^{i+1}$ with $d^{i+1}(t_n) \in I^{n+1} C^{i+2}$ and $t_{n+1} - t_n \in I^{n+1} C^{i+1}$ for all $n$ (the submodules $I^{n+1} \cdot \top$). Then there exist $a \in C^{i+1}$ and a sequence $Y : \mathbb N \to C^i$ such that $d^{i+1} a = 0$, and for every $n$ both $t_n - a - d^i(Y_n) \in I^{n+1} C^{i+1}$ and $Y_{n+1} - Y_n \in I^{n+1} C^i$.
--
--   This is the positive-degree existence half of the theorem on formal functions for a proper morphism over a complete Noetherian base, in Čech form: a formally compatible family of approximate $(i+1)$-cocycles is an honest algebraic cocycle plus the coboundary of a formally compatible family of $i$-cochains, up to an $I$-adically null error. It strengthens the variant in which the coboundary witness is produced separately for each $n$, the compatibility of the witnesses $Y_n$ being what is needed in the construction of cocycles from chart data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) :
    ∃ (a : F.cochain K (i + 1)) (Y : ℕ → F.cochain K i), F.d K (i + 1) a = 0 ∧
      (∀ n : ℕ, t n - a - F.d K i (Y n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) ∧
      (∀ n : ℕ, Y (n + 1) - Y n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K i))) := by sorry
