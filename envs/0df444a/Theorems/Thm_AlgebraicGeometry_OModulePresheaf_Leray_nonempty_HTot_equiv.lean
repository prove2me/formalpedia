-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/27d656b3-6c5d-53f7-99dd-10112d69af36
-- title:
--   Total cohomology of the Čech–Leray double complex
-- statement:
--   Let $R$ be a commutative ring, let $V'$ and $Z$ be schemes, let $p \colon V' \to Z$ be a morphism and $\pi_Z \colon Z \to \operatorname{Spec} R$ a morphism, and assume both $\pi_Z$ and the composite $p$ followed by $\pi_Z$ are separated. Let $K$ be an ordered affine cover of $Z$ and $K'$ one of $V'$, each consisting of a finite linearly ordered index type together with affine opens whose supremum is the whole scheme. Write $C^{\bullet,\bullet} =$ `LerayDblCpx p πZ K K'` for the associated bounded double complex of $R$-modules, with horizontal and vertical differentials squaring to zero and commuting, and with $C^{a,b}$ subsingleton once $a$ or $b$ reaches the maximum of the two index cardinalities; its total cohomology in degree $n$ is $\ker d_{\mathrm{Tot}}^n$ modulo the submodule which is $0$ for $n = 0$ and the preimage of the image of $d_{\mathrm{Tot}}^{n-1}$ otherwise, where $d_{\mathrm{Tot}} = d_H + (-1)^a d_V$. The assertion is that there exists an $R$-linear isomorphism in degree $0$ onto $\ker$ of the Čech differential on $0$-cochains of the module presheaf `OModulePresheaf.unit (p ≫ πZ)` (the structure sheaf $\mathcal O_{V'}$ with its $R$-module structure) relative to $K'$, and, for every $n$, an $R$-linear isomorphism in degree $n+1$ onto $\ker d^{\,n+1} / \operatorname{im} d^{\,n}$ for that same Čech complex. Only the existence of such isomorphisms is asserted, no specific map being named.
--
--   This is the degeneration of the Čech–Leray double complex associated with a morphism and a pair of ordered affine covers: its total cohomology computes the Čech cohomology of $\mathcal O_{V'}$ on the cover of the source, the input being exactness of the rows together with the compatibility of the vertical differential with the augmentation. It is used in the finiteness results for Čech cohomology of the structure sheaf, notably by [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K') ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (n + 1)
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n) := by sorry
