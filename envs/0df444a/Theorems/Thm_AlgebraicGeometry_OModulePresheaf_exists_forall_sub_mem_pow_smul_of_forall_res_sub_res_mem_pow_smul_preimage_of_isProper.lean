-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/78cc010d-c053-533a-b9da-985596015ff5
-- title:
--   Uniform Mittag-Leffler property for Čech 0-cochains along p
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, $q : P \to \operatorname{Spec} A$ a proper morphism of schemes and $p : V' \to P$ a further proper morphism. Let $G$ be an `OModulePresheaf` for the composite $p$ followed by $q$: a datum assigning to every open $U \subseteq V'$ an abelian group $G.\mathrm{obj}\,U$ carrying compatible $A$- and $\Gamma(V', U)$-module structures, together with $A$-linear restriction maps $G.\mathrm{res}$ for $U \le U'$ that are semilinear for restriction of scalars and satisfy the identity and composition laws. Assume $G$ is coherent, i.e. $G.\mathrm{obj}\,U$ is a finite $\Gamma(V',U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and $f \in \Gamma(V', U)$ every section over the basic open $D(f)$ becomes restricted from $U$ after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K'$ be an ordered affine cover of $V'$ (a finite linearly ordered index set $\iota$ with affine opens $K'.U\,i$ whose supremum is $\top$), let $W$ be an affine open of $P$, and let $n \in \mathbb{N}$. Write $W_i := K'.U\,i \sqcap p^{-1}W$ and $W_{ij} := W_i \sqcap W_j$. Then there is $c \in \mathbb{N}$ such that for every family $t = (t_i)_{i \in \iota}$ with $t_i \in G.\mathrm{obj}\,W_i$ satisfying $t_i|_{W_{ij}} - t_j|_{W_{ij}} \in I^{n+c} \cdot G.\mathrm{obj}\,W_{ij}$ for all $i, j$, there exists a family $a = (a_i)_{i \in \iota}$, $a_i \in G.\mathrm{obj}\,W_i$, with $a_i|_{W_{ij}} = a_j|_{W_{ij}}$ for all $i, j$ and $t_i - a_i \in I^{n} \cdot G.\mathrm{obj}\,W_i$ for all $i$.
--
--   This is the uniform Mittag-Leffler half of the theorem of formal functions (EGA III, théorème des fonctions formelles), in the relative form along $p$ and read off chart by chart on the base: a Čech $0$-cochain on the cover $(W_i)$ of $p^{-1}W$ which is a cocycle modulo $I^{n+c}$ agrees modulo $I^{n}$ with a genuine cocycle. It is the transport along $p$, over an affine chart $W$ of $P$, of the corresponding statement over an affine Noetherian base, [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper), and it feeds the construction of morphisms out of Čech pushforwards in [`AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_comp_eq_of_forall_ker_eq_pow_smul_top_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_sub_mem_pow_smul_of_forall_res_sub_res_mem_pow_smul_preimage_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ t : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (t i)
          - G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (t j)
          ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)))))) →
      ∃ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ i j : K'.ι,
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) ∧
        ∀ i : K'.ι, t i - a i ∈ I ^ n • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) := by sorry
