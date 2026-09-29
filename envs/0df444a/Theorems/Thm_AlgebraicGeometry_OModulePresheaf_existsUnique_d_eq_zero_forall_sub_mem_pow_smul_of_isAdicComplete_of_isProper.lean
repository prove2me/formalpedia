-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b81facf4-4f8d-5f2d-b1b4-318d1381202c
-- title:
--   Degree-0 theorem on formal functions: unique limit cocycle
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal for which $A$ is $I$-adically complete (and separated), and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Let $F$ be an `OModulePresheaf` over $q$, i.e. data assigning to each open $U \subseteq P$ an abelian group $F.obj\,U$ with compatible $A$-module and $\Gamma(P,U)$-module structures ($A$ acting through $q$) together with $A$-linear restriction maps satisfying the presheaf identities and $\Gamma$-semilinearity. Assume $F$ is coherent, i.e. $F.obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $P_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $P_f$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index set with affine opens $U_i$ whose supremum is $\top$, with $i$-cochains $F.cochain\,K\,i$ the families of sections of $F$ over the intersections $\bigsqcap_j U_{s(j)}$ indexed by $s \in K.Idx\,i$, and let `F.d K 0` be the degree-$0$ Čech differential. Let $(t_n)_{n \ge 0}$ be $0$-cochains with $F.d\,K\,0\,(t_n) \in I^{n+1} \cdot F.cochain\,K\,1$ and $t_{n+1} - t_n \in I^{n+1} \cdot F.cochain\,K\,0$ for all $n$. Then there is exactly one $0$-cochain $a$ with $F.d\,K\,0\,a = 0$ and $a - t_n \in I^{n+1} \cdot F.cochain\,K\,0$ for every $n$.
--
--   This is the degree-$0$ case of the theorem on formal functions for a coherent sheaf on a proper scheme over a complete Noetherian base, in Čech form: a system of $0$-cochains that are cocycles modulo $I^{n+1}$ and compatible modulo $I^{n+1}$ converges to a unique genuine $0$-cocycle, so that $\check H^0$ maps bijectively onto the inverse limit of the $\check H^0(\mathfrak U, F/I^{n+1}F)$. It is assembled from the two uniform Artin–Rees statements in degree $0$ together with $I$-adic completeness of the finite $A$-module $\check H^0$, and is used in the construction of formal charts and in the comparison of sections with their reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by sorry
