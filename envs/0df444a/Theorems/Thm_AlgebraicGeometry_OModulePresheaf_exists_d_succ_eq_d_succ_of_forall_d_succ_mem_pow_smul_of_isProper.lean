-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/0d923378-016c-52d8-8403-2f562478c237
-- title:
--   Uniform Artin–Rees for Čech coboundaries in positive degree
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Let $F$ be an `OModulePresheaf` over $q$, i.e. an assignment of an $A$-module and compatible $\Gamma(P,U)$-module structure to each open $U \subseteq P$, together with $A$-linear restriction maps along inclusions that are semilinear for the restriction of functions and satisfy the presheaf identities; assume $F$ is coherent, in the sense that $F.\mathrm{obj}\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent, in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open set $P_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $P_f$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index set $\iota$ together with affine opens $U_i$ whose supremum is $P$; for $j \in \mathbb{N}$ the index set $K.\mathrm{Idx}\,j$ consists of the strictly monotone maps $\mathrm{Fin}(j+1) \to \iota$, $K.\mathrm{inter}\,s$ is the intersection of the corresponding opens, and $F.\mathrm{cochain}\,K\,j$ is the product of the modules $F.\mathrm{obj}(K.\mathrm{inter}\,s)$ over $s \in K.\mathrm{Idx}\,j$, with the degree-raising maps `F.d K j` as alternating Čech differentials. Then for all $i, n \in \mathbb{N}$ there exists $c \in \mathbb{N}$ such that for every cochain $w \in F.\mathrm{cochain}\,K\,(i+1)$ whose coboundary satisfies, componentwise, $(F.d\,K\,(i+1)\,w)(s) \in I^{n+c} \cdot F.\mathrm{obj}(K.\mathrm{inter}\,s)$ for all $s \in K.\mathrm{Idx}\,(i+2)$, there is a cochain $w' \in F.\mathrm{cochain}\,K\,(i+1)$ with $w'(s) \in I^{n} \cdot F.\mathrm{obj}(K.\mathrm{inter}\,s)$ for all $s \in K.\mathrm{Idx}\,(i+1)$ and $F.d\,K\,(i+1)\,w' = F.d\,K\,(i+1)\,w$.
--
--   This is a uniform Artin–Rees statement for the alternating Čech complex of a coherent module datum on a proper $A$-scheme: coboundaries lying in $I^{n+c}$ already come from cochains in $I^{n}$, with $c$ independent of the cochain. It feeds the comparison of $I$-adic filtrations underlying the theorem on formal functions, and is cited by [`AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K (i + 1),
      (∀ s : K.Idx (i + 2), F.d K (i + 1) w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K (i + 1),
        (∀ s : K.Idx (i + 1), w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K (i + 1) w' = F.d K (i + 1) w := by sorry
