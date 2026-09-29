-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/75ee7cf1-dbc7-5d14-8782-626a9f63b6b8
-- title:
--   Uniform Artin–Rees bound for Čech 0-coboundaries, coherent case
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. Let $F$ be module data on the opens of $P$ over $q$: an abelian group $F(U)$ for each open $U \subseteq P$ carrying both an $A$-module and a $\Gamma(P,U)$-module structure, compatible through the algebra map $A \to \Gamma(P,U)$ induced by $q$, together with $A$-linear restriction maps that are semilinear for the sections and satisfy the usual identity and composition laws. Assume $F$ is coherent in the sense that $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$ each element of $F(D(f))$ becomes the restriction of an element of $F(U)$ after multiplication by some power of $f$, and each element of $F(U)$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K$ be a finite family of affine opens $U_i$, indexed by a linearly ordered finite type, whose supremum is $\top$; for a strictly monotone $s : \{0,\dots,i\} \to \iota$ write $U_s$ for the intersection of the corresponding $U_{s(j)}$, and let $d^0 : \prod_i F(U_i) \to \prod_{i<j} F(U_i \cap U_j)$ be the alternating Čech coboundary. Then for every $n \in \mathbb{N}$ there exists $c \in \mathbb{N}$ such that every $0$-cochain $w$ all of whose coboundary components $d^0w(s)$ lie in $I^{n+c} \cdot F(U_s)$ admits a $0$-cochain $w'$ with all components $w'(s) \in I^n \cdot F(U_s)$ and $d^0 w' = d^0 w$, the submodules being formed for the $A$-module structures.
--
--   This is the uniform Artin–Rees, or Mittag-Leffler, input to the theorem on formal functions in degree $0$: coboundaries lying deeply in the $I$-adic filtration are coboundaries of correspondingly deep $0$-cochains, with a bound $c$ independent of the cochain. It is used in the proof that global sections over an $I$-adically complete base are determined by their reductions, namely in [`AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper), and is deduced from the corresponding statement for the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K 0,
      (∀ s : K.Idx 1, F.d K 0 w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K 0,
        (∀ s : K.Idx 0, w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K 0 w' = F.d K 0 w := by sorry
