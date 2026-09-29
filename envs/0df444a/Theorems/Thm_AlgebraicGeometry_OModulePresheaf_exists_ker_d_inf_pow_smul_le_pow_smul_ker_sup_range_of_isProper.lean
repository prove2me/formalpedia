-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/93a8eb47-c7dc-5c78-bbdb-5f7f1f6d2d0b
-- title:
--   Artin–Rees separatedness for Čech cocycles in degree i+1
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. Let $F$ be an `OModulePresheaf` over $q$, that is, an assignment to each open $U \subseteq P$ of an $A$-module which is simultaneously a $\Gamma(P,U)$-module compatibly with the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$, together with $A$-linear restriction maps along inclusions $U \le U'$ that are semilinear for restriction of sections and satisfy the identity and composition laws. Assume $F$ is coherent, i.e. $F.\mathrm{obj}\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and $f \in \Gamma(P,U)$ every section over the basic open $P_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $P_f$ is killed by a power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index set together with affine opens $U_i$ whose supremum is $P$. Let $i, n$ be natural numbers. Then there is $c \in \mathbb{N}$ such that, in the cochain module $F.\mathrm{cochain}\,K\,(i+1) = \prod_{s} F.\mathrm{obj}(\bigcap_j U_{s(j)})$ with its $A$-linear differentials `F.d`, $$\ker d^{\,i+1} \cap I^{n+c}\,C^{i+1} \subseteq I^{n}\,\ker d^{\,i+1} + \operatorname{im} d^{\,i}.$$
--
--   This is the uniform Artin–Rees, or separatedness, estimate on Čech cocycles of degree $i+1$: the filtration induced on cohomology by the $I$-adic filtration of the cochains is cofinal with the $I$-adic filtration of cohomology. It feeds the two formal-functions statements over an $I$-adically complete base, [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper) and [`AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, LinearMap.ker (F.d K (i + 1)) ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) ≤
      I ^ n • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by sorry
