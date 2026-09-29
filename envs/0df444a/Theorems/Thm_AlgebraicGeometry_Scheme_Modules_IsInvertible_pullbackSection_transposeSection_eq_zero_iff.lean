-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d58a7e0f-b16d-52d5-bb2c-94f70d452218
-- title:
--   Pull-back of a transpose section vanishes iff the map does
-- statement:
--   Let $Y$ and $Y'$ be schemes, $g : Y' \to Y$ a morphism, and let $X$, $M$ be sheaves of modules on $Y$ (objects of `Y.Modules`). Assume `Scheme.Modules.IsInvertible X`, i.e. every point of $Y$ has an open neighbourhood $U$ such that the pull-back of $X$ along the open immersion $U \hookrightarrow Y$ is isomorphic to the unit sheaf of modules on $U$. Let $\varphi : X \to M$ be a morphism, write $X^{\vee}$ for `Scheme.Modules.dual X`, the internal hom $(\mathrm{ihom}\,X)(\mathbf 1)$ into the unit object, and let $s : \mathbf 1 \to M \otimes X^{\vee}$ be a morphism which is a transpose of $\varphi$ in the sense that the evaluation $(\mathrm{ihom.ev}\,X)$ at $\mathbf 1$, namely $X \otimes X^{\vee} \to \mathbf 1$, followed by $s$ equals $\varphi \triangleright X^{\vee} : X \otimes X^{\vee} \to M \otimes X^{\vee}$. Then the pulled-back section $\mathbf 1_{Y'} \to g^{*}(M \otimes X^{\vee})$, defined as the inverse of the canonical isomorphism $g^{*}\mathbf 1_{Y} \cong \mathbf 1_{Y'}$ followed by $g^{*}s$, is zero if and only if $g^{*}\varphi = 0$.
--
--   This is the base-change compatibility of the transpose of a morphism out of an invertible module, stated directly as an equivalence of vanishing statements, so that no comparison isomorphism $g^{*}(M \otimes X^{\vee}) \cong g^{*}M \otimes (g^{*}X)^{\vee}$ has to be exhibited. It is used in the construction of relative effective Cartier divisors representing a line bundle, in [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre) and its variant for divisors supported in a given closed subset, where the transpose of an evaluation map is restricted to fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 := by sorry
