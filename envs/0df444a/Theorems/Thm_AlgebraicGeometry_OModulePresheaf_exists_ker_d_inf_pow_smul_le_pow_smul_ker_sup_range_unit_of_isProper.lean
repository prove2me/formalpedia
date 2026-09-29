-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/f95f4db2-41cc-54d9-9e17-62293d7e3286
-- title:
--   Artin–Rees for Čech cocycles of mathcal O_P, positive degree
-- statement:
--   Let $A$ be a Noetherian commutative ring and $I \subseteq A$ an ideal, let $P$ be a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism, let $K$ be an ordered affine cover of $P$ (a finite linearly ordered index type $\iota$ together with affine opens $U_j \subseteq P$, $j \in \iota$, whose supremum is all of $P$), and let $i, n$ be natural numbers. Consider the $\mathcal O$-module presheaf `OModulePresheaf.unit q`, which assigns to an open $U \subseteq P$ the ring $\Gamma(P, U)$, viewed as an $A$-module through the algebra structure induced by $q$, with the presheaf restrictions as transition maps, and its associated Čech-type cochain modules $C^k = \prod_{s} \Gamma(P, K.\mathrm{inter}\, s)$, the product over indices $s$ of degree $k$, where $K.\mathrm{inter}\, s = \bigcap_j K.U(s_j)$ is the intersection of the members of the cover along the tuple $s$, together with the $A$-linear differentials $d$. The assertion is that there exists $c \in \mathbb N$ such that, as $A$-submodules of $C^{i+1}$, $$\ker d^{i+1} \cap I^{n+c} C^{i+1} \;\le\; I^{n} \ker d^{i+1} + \operatorname{im} d^{i}.$$
--
--   This is the structure-sheaf instance, in cochain degree $i+1$, of the uniform Artin–Rees-type separatedness statements for Čech cocycles on a proper scheme over a Noetherian base, of the kind underlying the theorem on formal functions and the finiteness and comparison theorems for proper morphisms. It is cited in the proof of the corresponding statement [`AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, LinearMap.ker ((OModulePresheaf.unit q).d K (i + 1)) ⊓
        I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q).cochain K (i + 1))) ≤
      I ^ n • LinearMap.ker ((OModulePresheaf.unit q).d K (i + 1)) ⊔
        LinearMap.range ((OModulePresheaf.unit q).d K i) := by sorry
