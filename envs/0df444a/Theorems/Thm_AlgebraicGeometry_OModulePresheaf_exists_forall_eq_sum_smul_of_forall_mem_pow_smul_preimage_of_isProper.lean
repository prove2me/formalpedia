-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/84683156-a629-5156-a888-cdcdee96b152
-- title:
--   Separatedness half of formal functions, relative chart version
-- statement:
--   Fix a Noetherian commutative ring $A$ and an ideal $I \subseteq A$, a scheme $P$ with a proper morphism $q : P \to \operatorname{Spec} A$, and a scheme $V'$ with a proper morphism $p : V' \to P$. Let $G$ be an `OModulePresheaf` for the morphism $p$ followed by $q$: an assignment of an $A$-module $G(U)$ to each open $U \subseteq V'$ which is also a $\Gamma(V',U)$-module compatibly with the $A$-algebra structure coming from the morphism to $\operatorname{Spec} A$, together with $A$-linear restrictions $G(U') \to G(U)$ for $U \le U'$ that are semilinear over the restriction of functions and satisfy the identity and composition laws. Assume $G$ is coherent, i.e. $G(U)$ is a finite $\Gamma(V',U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and every $f \in \Gamma(V',U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, a restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K'$ be an ordered affine cover of $V'$, that is, a finite linearly ordered index set $\iota$ together with affine opens $K'_i$ whose supremum is $V'$; let $W$ be an affine open of $P$ and $n \in \mathbb{N}$. Write $W_i := K'_i \cap p^{-1}W$. Then there is $c \in \mathbb{N}$, depending only on these data, such that for every family $a = (a_i)_{i \in \iota}$ with $a_i \in G(W_i)$ satisfying the cocycle condition that $a_i$ and $a_j$ have the same restriction to $W_i \cap W_j$ for all $i,j$, and with $a_i \in I^{n+c} \cdot G(W_i)$ for every $i$, there exist $m \in \mathbb{N}$, scalars $r_1,\dots,r_m \in I^n$ and families $b_1,\dots,b_m$, each $b_l = (b_{l,i})_i$ with $b_{l,i} \in G(W_i)$ and each satisfying the same cocycle condition, such that $a = \sum_{l} r_l \cdot b_l$.
--
--   This is the separatedness (injectivity) half of the theorem on formal functions for a proper morphism, in the form needed chart by chart along $p$: Čech $0$-cocycles on $p^{-1}W$ whose components are $I^{n+c}$-divisible lie in $I^n$ times the module of cocycles, i.e. the kernel of $(p_*G)(W) \to p_*(G/I^{n+c}G)(W)$ is contained in $I^n (p_*G)(W)$. It is obtained from the absolute statement [`AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper) over $\operatorname{Spec} A$, and is used in the construction of morphisms out of the Čech pushforward whose kernels are powers of $I$ times everything.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsProper p]
    (G : OModulePresheaf (p ≫ q)) (hc : G.IsCoherent) (hqc : G.IsQuasicoherent)
    (K' : V'.OrderedAffineCover) (W : P.affineOpens) (n : ℕ) :
    ∃ c : ℕ, ∀ a : (∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
      (∀ i j : K'.ι,
        G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (a i)
          = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (a j)) →
      (∀ i : K'.ι, a i ∈ I ^ (n + c) • (⊤ : Submodule A (G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))))) →
      ∃ (m : ℕ) (r : Fin m → A) (b : Fin m → ∀ i : K'.ι, G.obj (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))),
        (∀ l, r l ∈ I ^ n) ∧
        (∀ (l : Fin m) (i j : K'.ι),
          G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (b l i)
            = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (b l j)) ∧
        a = ∑ l, r l • b l := by sorry
