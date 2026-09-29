-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/51e5122f-cba1-5ab2-9e19-03a4fd2f3f46
-- title:
--   Uniform Artin–Rees for Čech coboundaries of 𝒪_P
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism, let $K$ be an ordered affine cover of $P$ — a finite linearly ordered index type $K.\iota$ together with opens $K.U_j$, each affine, whose supremum is $\top$ — and let $i, n$ be natural numbers. Work with the presheaf of modules `OModulePresheaf.unit q`, which assigns to an open $U$ the ring $\Gamma(P, U)$, regarded as an $A$-module through the algebra structure induced by $q$, with restriction maps the presheaf restrictions. Its cochains in degree $j$ are families indexed by the strictly monotone maps $s : \mathrm{Fin}(j+1) \to K.\iota$, a cochain assigning to $s$ an element of $\Gamma(P, K.\mathrm{inter}\,s)$ where $K.\mathrm{inter}\,s = \bigsqcap_k K.U_{s(k)}$, and `d` denotes the alternating Čech differential. The assertion is the existence of a natural number $c$, depending only on the data and on $i$ and $n$ and not on the cochain, such that for every cochain $w$ of degree $i+1$ whose coboundary satisfies $(d^{\,i+1}w)_s \in I^{n+c} \cdot \Gamma(P, K.\mathrm{inter}\,s)$ for every strictly monotone $s : \mathrm{Fin}(i+3) \to K.\iota$, there is a cochain $w'$ of degree $i+1$ with $w'_s \in I^{n} \cdot \Gamma(P, K.\mathrm{inter}\,s)$ for every strictly monotone $s : \mathrm{Fin}(i+2) \to K.\iota$ and with $d^{\,i+1}w' = d^{\,i+1}w$.
--
--   This is a uniform Artin–Rees statement for the alternating Čech complex of the structure sheaf of a proper scheme over a Noetherian base: a coboundary that is divisible to order $n+c$ already comes from a cochain divisible to order $n$, with $c$ independent of the cochain. It is the structure-sheaf case in degree $i+1$, and is used to derive the corresponding statement for general coherent quasi-coherent module presheaves, [`AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper); the finiteness input comes from `cechFinite_of_isProper` together with $d \circ d = 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K (i + 1),
      (∀ s : K.Idx (i + 2), (OModulePresheaf.unit q).d K (i + 1) w s ∈
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).obj (K.inter s)))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K (i + 1),
        (∀ s : K.Idx (i + 1), w' s ∈ I ^ n • (⊤ : Submodule A ((OModulePresheaf.unit q).obj (K.inter s)))) ∧
        (OModulePresheaf.unit q).d K (i + 1) w' = (OModulePresheaf.unit q).d K (i + 1) w := by sorry
