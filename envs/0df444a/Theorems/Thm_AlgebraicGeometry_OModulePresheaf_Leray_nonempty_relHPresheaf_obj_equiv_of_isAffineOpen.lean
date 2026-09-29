-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/a9969d21-c40d-5912-a386-df0a8d2b8659
-- title:
--   Relative Čech presheaves on an affine base open
-- statement:
--   Let $R$ be a commutative ring, let $V'$ and $Z$ be schemes (all in one universe), let $p \colon V' \to Z$ be a morphism and let $\pi_Z \colon Z \to \operatorname{Spec} R$ be a separated morphism. Let $K'$ be an ordered affine cover of $V'$, that is, a finite linearly ordered index set together with affine opens $K'_i \subseteq V'$ whose supremum is $\top$, and let $U \subseteq Z$ be an open subscheme with `hU : IsAffineOpen U`. Write $\mathcal{K}$ for the ordered affine cover `restrictToPreimage p πZ K' hU` of the open $p^{-1}U$, with the same index set and members $K'_i \cap p^{-1}U$, each affine because $\pi_Z$ is separated and $U$ is affine. The assertion is twofold. First, the value at $U$ of the degree-$0$ relative cohomology presheaf `relHPresheaf p πZ K' 0`, namely the quotient of $\ker(\mathrm{relAltd}\ p\ \pi_Z\ K'\ U\ 0)$ by the submodule `relAltHB p πZ K' U 0`, admits an $R$-linear isomorphism onto the degree-$0$ Čech cohomology of $\mathcal{K}$ for the structure sheaf, i.e. the kernel of the Čech differential $\mathcal{K}.d\ (p \gg \pi_Z)\ 0$. Second, for every $b \in \mathbb{N}$ the value at $U$ of `relHPresheaf p πZ K' (b+1)` admits an $R$-linear isomorphism onto $\ker(\mathcal{K}.d\ (p \gg \pi_Z)\ (b+1))$ modulo the coboundaries from degree $b$. Both claims are stated as nonemptiness of the respective types of $R$-linear equivalences, so no particular comparison map is singled out.
--
--   This is the local comparison underlying the Leray-style double complex for $p \colon V' \to Z$ over $\operatorname{Spec} R$: over an affine open $U$ of the base, the relative Čech construction computes exactly the Čech cohomology of the structure sheaf for the restricted cover $(K'_i \cap p^{-1}U)_i$ of $p^{-1}U$, the degree-$0$ case being recorded separately because there the target is a kernel rather than a quotient. It is used in the study of the relative cohomology presheaves, in particular by [`AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ]
    (K' : V'.OrderedAffineCover) {U : Z.Opens} (hU : IsAffineOpen U) :
    Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' 0).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).H0 (p ≫ πZ)) ∧
      ∀ b : ℕ, Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' (b + 1)).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b) := by sorry
