-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4ad0e894-ec8a-52f0-9694-ad21511179ac
-- title:
--   Vanishing of I-adically divisible Čech 0-cocycles over proper schemes
-- statement:
--   Let $A$ be a Noetherian commutative ring and $I \subseteq A$ an ideal such that $A$ is complete and separated for the $I$-adic topology. Let $P$ be a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. Let $F$ be an `OModulePresheaf` for $q$: an assignment to each open $U \subseteq P$ of an abelian group $F.obj\,U$ carrying compatible $A$- and $\Gamma(P, U)$-module structures (the scalar tower being taken along the algebra structure induced by $q$), together with $A$-linear restriction maps $F.res$ for $U \le U'$ which are semilinear for the restriction of functions, reflexive and compatible with composition. Assume $F$ is coherent in the sense that $F.obj\,U$ is a finite $\Gamma(P, U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P, U)$, each element of $F.obj\,(D(f))$ becomes, after multiplication by some power of $f$, the restriction of an element of $F.obj\,U$, and each element of $F.obj\,U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$, i.e. a finite linearly ordered index type $\iota$ with affine opens $U_i$ whose supremum is $\top$. Let $z$ be a $0$-cochain for $K$, that is a family $z_s \in F.obj(\bigsqcap_j U_{s(j)})$ indexed by the strictly monotone maps $s : \mathrm{Fin}\,1 \to \iota$, such that the Čech coboundary `F.d K 0` of $z$ vanishes. If for every $k \in \mathbb{N}$ and every index $s$ the element $z_s$ lies in $I^k \cdot F.obj(\bigsqcap_j U_{s(j)})$ (as $A$-submodule), then $z = 0$.
--
--   This is the injectivity, or Krull separatedness, half of the theorem on formal functions for a proper morphism over an $I$-adically complete Noetherian base, formulated for coherent module data presented by an ordered affine cover and its Čech complex in degree $0$. It is used in the proof that a morphism prescribed formally over $\operatorname{Spec} A$ extends uniquely, [`AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (z : F.cochain K 0) (hz : F.d K 0 z = 0)
    (h : ∀ (k : ℕ) (s : K.Idx 0), z s ∈ I ^ k • (⊤ : Submodule A (F.obj (K.inter s)))) :
    z = 0 := by sorry
