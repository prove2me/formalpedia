-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
-- name    : AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/35aa3040-34fe-523b-8d52-5569565c618e
-- title:
--   Čech vanishing is local on the base via bi-Čech
-- statement:
--   Fix a commutative ring $R$, schemes $P$ and $Y$, a separated morphism $\pi\colon P\to\operatorname{Spec}R$, and a morphism $q\colon P\to Y$. Let $\mathfrak V$ be an ordered affine cover of $Y$, that is, a finite linearly ordered index set together with affine opens $\mathfrak V.U_i$ whose supremum is $\top$, and assume every pairwise intersection $\mathfrak V.U_i\sqcap\mathfrak V.U_j$ is again affine open. Let $N$ be an $\mathcal O_P$-module object on $P$, and assume the presheaf `ofModules` $\pi$ $N$, whose sections on $U$ are $\Gamma(N,U)$ with the $R$-structure induced by $\pi$, satisfies `IsQuasicoherent`: for every affine open $U$ and $f\in\Gamma(P,U)$, every section over the basic open $P_f$ becomes, after multiplication by some power of $f$, a restriction from $U$, and every section over $U$ restricting to $0$ on $P_f$ is annihilated by a power of $f$. Assume further that for each $i\in\mathbb N$ and each strictly monotone $s\colon \operatorname{Fin}(i+1)\to\mathfrak V.\iota$ the open subscheme $q^{-1}\bigl(\bigsqcap_j\mathfrak V.U_{s(j)}\bigr)$ of $P$ admits at least one ordered affine cover for which the alternating Čech complex of the restriction of $N$ has $H^0=\bot$ and all higher cohomology groups $\mathrm{HSucc}\,j$ (the quotient of $\ker d^{j+1}$ by the image of $d^{j}$) subsingletons. Then for every ordered affine cover $\mathfrak W$ of $P$ one has $H^0(\mathfrak W, N)=\bot$ and $\mathrm{HSucc}\,j$ is a subsingleton for all $j$.
--
--   This is the descent half of the Cartan–Leray comparison in the Čech formulation: vanishing of the alternating Čech cohomology of a quasi-coherent datum on the preimages of the members and intersections of a finite affine cover of the base propagates to the total space, and, by cover independence, to an arbitrary finite ordered affine cover of $P$. It is used in the treatment of polarisations, where a line-bundle comparison over a base is reduced to vanishing over the affine pieces of that base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_idx_preimage_of_isAffineOpen_inf
    {R : Type u} [CommRing R] {P Y : Scheme.{u}} (π : P ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (q : P ⟶ Y) (𝔙 : Y.OrderedAffineCover) (hVV : ∀ i j, IsAffineOpen (𝔙.U i ⊓ 𝔙.U j))
    (N : P.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (hV : ∀ (i : ℕ) (s : 𝔙.Idx i), ∃ 𝔚 : ((q ⁻¹ᵁ 𝔙.inter s : P.Opens) : Scheme.{u}).OrderedAffineCover,
      (OModulePresheaf.ofModules ((q ⁻¹ᵁ 𝔙.inter s).ι ≫ π) (N.restrict (q ⁻¹ᵁ 𝔙.inter s).ι)).H0 𝔚 = ⊥ ∧
        ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules ((q ⁻¹ᵁ 𝔙.inter s).ι ≫ π) (N.restrict (q ⁻¹ᵁ 𝔙.inter s).ι)).HSucc 𝔚 j))
    (𝔚 : P.OrderedAffineCover) :
    (OModulePresheaf.ofModules π N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔚 j) := by sorry
