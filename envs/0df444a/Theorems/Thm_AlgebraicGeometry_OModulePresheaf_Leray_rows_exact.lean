-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.rows_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/94261731-51f0-54c9-8407-16fcfd8a826e
-- title:
--   Exactness of the rows of the Čech–Leray double complex
-- statement:
--   Fix a commutative ring $R$, schemes $V'$ and $Z$, a morphism $p \colon V' \to Z$ and a morphism $\pi_Z \colon Z \to \operatorname{Spec} R$, and assume both $\pi_Z$ and the composite $p$ followed by $\pi_Z$ are separated. Let $K$ be an ordered affine cover of $Z$ (a finite linearly ordered index set together with affine opens whose supremum is $\top$) and $K'$ one of $V'$. The associated bounded double complex of $R$-modules `LerayDblCpx p πZ K K'` has $(a,b)$-term the product, over strictly increasing chains $\sigma$ of length $a+1$ in $K$ and $\tau$ of length $b+1$ in $K'$, of $\Gamma(V', U'_\tau \cap p^{-1}U_\sigma)$, where $U_\sigma$, $U'_\tau$ denote the intersections along the chains and $R$ acts through the composite morphism; its horizontal differential `dH a b` is the alternating sum over the $a+2$ faces of $\sigma$ of the restriction maps, and `biAug p πZ K K' b` sends a Čech $b$-cochain $(s_\tau)$ of the structure sheaf for $K'$ to the family of restrictions of $s_\tau$ to $U'_\tau \cap p^{-1}U_\sigma$. The assertion is threefold: for all $a, b$ the kernel of `dH (a+1) b` is contained in the image of `dH a b`; for all $b$ the kernel of `dH 0 b` equals the range of `biAug … b`; and each `biAug … b` is injective.
--
--   This is the row-exactness half of the Čech–Leray comparison: each row of the double complex is, for a fixed chain $\tau$ in $K'$, the augmented Čech complex of the structure sheaf on the affine open $U'_\tau$ with respect to the affine cover by the opens $U'_\tau \cap p^{-1}U_\sigma$, so it is acyclic with augmentation the Čech cochains of $K'$. It feeds the identification of the total cohomology of the double complex with Čech cohomology for $K'$, and thence the comparison results for sections and differentials obtained from charts upstairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.rows_exact
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ a b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH (a + 1) b)
        ≤ LinearMap.range ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH a b)) ∧
      (∀ b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH 0 b)
        = LinearMap.range (OModulePresheaf.Leray.biAug p πZ K K' b)) ∧
      ∀ b : ℕ, Function.Injective (OModulePresheaf.Leray.biAug p πZ K K' b) := by sorry
