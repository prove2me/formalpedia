-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul
-- name    : AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/fd718026-bb5b-5e70-9f3b-8bb0582a2b44
-- title:
--   Endomorphisms of the unit mathcal O_X-module are multiplications
-- statement:
--   Let $X$ be a scheme and let $\mathbf 1_{X.\mathrm{Modules}}$ denote the unit object of the monoidal category `X.Modules` of $\mathcal O_X$-modules, whose sections over an open $U \subseteq X$ are, by construction, the elements of $\Gamma(X, U)$, with the $\Gamma(X,U)$-action given by multiplication in $\Gamma(X,U)$ and the restriction maps those of $X.\mathrm{presheaf}$. Let $c$ be an endomorphism of this unit object, let $U$ be an open subset of $X$, and let $m$ be a section of the unit object over $U$, viewed as an element of $\Gamma(X, U)$. The assertion is the identity in $\Gamma(X, U)$
--   $$c_U(m) \;=\; \bigl(c_{\top}(1)\bigr)\big|_U \cdot m ,$$
--   where $c_{\top}(1) \in \Gamma(X, \top) = \Gamma(X, \mathcal O_X)$ is the value of the component of $c$ at the top open on the unit section $1$, and the restriction along $U \le \top$ is taken by $X.\mathrm{presheaf}$ applied to the opposite of the inclusion `homOfLE (le_top)`. Thus every endomorphism of the unit module acts on all local sections as multiplication by the single global function $c_{\top}(1)$.
--
--   This is the computational half of the classical identification $\operatorname{End}_{\mathcal O_X}(\mathcal O_X) \cong \Gamma(X, \mathcal O_X)$: an endomorphism of the unit object is multiplication by its value on the global section $1$. It is used downstream to decide when such an endomorphism is nonzero or invertible, in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral) and in the construction of isomorphisms with the unit object in [`GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_ne_zero_section_dual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul
    {X : Scheme.{u}} (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    (show Γ(X, U) from c.app U m) =
      X.presheaf.map (homOfLE (le_top (a := U))).op (show Γ(X, ⊤) from c.app ⊤ (1 : Γ(X, ⊤))) *
        (show Γ(X, U) from m) := by sorry
