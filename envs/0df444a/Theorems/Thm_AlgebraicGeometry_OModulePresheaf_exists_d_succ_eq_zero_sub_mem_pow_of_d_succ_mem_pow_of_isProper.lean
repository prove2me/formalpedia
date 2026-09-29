-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/81171011-769a-56a2-b934-b38c1bef90a2
-- title:
--   Uniform Artin–Rees for Čech cocycles in degree i+1
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. Let $F$ be module data of type `OModulePresheaf q` on $P$: an assignment to each open $U \subseteq P$ of an abelian group $F.obj\,U$ carrying compatible module structures over $A$ and over $\Gamma(P,U)$ (compatible via the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$), together with $A$-linear restriction maps for $U \le U'$ that are semilinear for restriction of sections, reflexive and transitive. Assume $F$ is coherent, i.e. $F.obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and $f \in \Gamma(P,U)$ every element of $F.obj\,(D(f))$ becomes the restriction of an element of $F.obj\,U$ after multiplication by some power of $f$, and every element of $F.obj\,U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index set with affine opens $U_j$ whose supremum is $\top$; the associated cochain module in degree $i$ is the product $\prod_{s} F.obj(\bigcap_j K.U(s_j))$ over the index tuples $s$ of that degree, with differential $F.d$. Then for all $i, n \in \mathbb{N}$ there is $c \in \mathbb{N}$ such that every cochain $t$ of degree $i+1$ with $F.d\,t \in I^{n+c} \cdot (\text{all of the degree-}(i+2)\text{ cochains})$ admits a cochain $a$ of degree $i+1$ with $F.d\,a = 0$ and $t - a \in I^{n} \cdot (\text{all of the degree-}(i+1)\text{ cochains})$.
--
--   This is the uniform Artin–Rees (Mittag-Leffler) statement for the alternating Čech complex of a coherent module on a proper $A$-scheme in positive degree: a cochain that is a cocycle modulo a sufficiently high power of $I$ differs from a genuine cocycle by a cochain in $I^n$. It feeds the existence half of the theorem on formal functions in degree $i+1$, being cited by [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper) and [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K (i + 1),
      F.d K (i + 1) t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 2))) →
      ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
        t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K (i + 1))) := by sorry
