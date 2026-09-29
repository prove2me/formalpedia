-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4a526b74-7ad1-55db-b3da-8dfe68a13a9e
-- title:
--   Artin–Rees for Čech 0-cocycles over a proper base
-- statement:
--   Let $A$ be a commutative Noetherian ring and $I \subseteq A$ an ideal, let $P$ be a scheme and let $q : P \to \operatorname{Spec} A$ be a proper morphism. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq P$, each an affine open, whose supremum is all of $P$. Consider the presheaf of modules $(\mathrm{unit}\ q)$, which assigns to an open $U$ the ring $\Gamma(P, U)$ of sections, viewed as an $A$-algebra via $q$ and as a module over itself, with the presheaf restriction maps as transition maps. For it, $\mathrm{cochain}\ K\ 0$ is the $A$-module of Čech $0$-cochains, the product over the $0$-simplices $s$ of $K$ of $\Gamma(P, \bigsqcap_j U_{s(j)})$, and its submodule $\mathrm{H0}\ K$ is the kernel of the Čech differential in degree $0$, i.e. the $0$-cocycles. Then for every natural number $n$ there is a natural number $c$ such that, inside the $A$-module of $0$-cochains, the intersection of the submodule of $0$-cocycles with $I^{n+c} \cdot C^0$ is contained in $I^n$ times the submodule of $0$-cocycles.
--
--   This is the uniform Artin–Rees statement for the filtration of Čech $0$-cocycles of the structure sheaf induced by the powers of $I$, the assertion being that this filtration is $I$-good, so that the topology it induces on global sections over the charts is the $I$-adic one. It rests on finiteness of Čech data for coherent quasi-coherent presheaves over a proper morphism to a Noetherian base, via [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper), and feeds the variant [`AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, (OModulePresheaf.unit q).H0 K ⊓
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K 0)) ≤
      I ^ n • (OModulePresheaf.unit q).H0 K := by sorry
