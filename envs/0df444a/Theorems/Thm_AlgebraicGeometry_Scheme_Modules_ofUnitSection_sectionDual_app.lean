-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
-- name    : AlgebraicGeometry.Scheme.Modules.ofUnitSection_sectionDual_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/4dc58c83-f299-51c5-b32e-cf72ffcef305
-- title:
--   s^∨(t) equals the coefficient of s along t
-- statement:
--   Let $X$ be a scheme and $M$ a sheaf of modules on $X$, and let $s \colon \mathbf{1}_{X\text{-Mod}} \to M$ be a morphism from the unit object of the monoidal category `X.Modules`, i.e. a global section of $M$. Let $U$ be an open of $X$ and let $t$ be a section over $U$ of the dual $\mathrm{dual}\,M = (\mathrm{ihom}\,M)(\mathbf{1})$, the internal Hom sheaf $\mathcal{H}om(M,\mathcal O_X)$. On the left-hand side, `sectionDual s` is the morphism $\mathrm{dual}\,M \to \mathbf{1}$ given by precomposition with $s$ on internal Homs, `(MonoidalClosed.pre s).app (𝟙_ X.Modules)`, followed by the isomorphism $\mathcal{H}om(\mathcal O_X,\mathcal O_X) \cong \mathcal O_X$; its component at $U$ sends $t$ into $\Gamma(\mathbf{1},U)$, and `ofUnitSection U` reads this as an element of $\Gamma(X,U)$. On the right-hand side, `ihomSectionsEquiv M (𝟙_ X.Modules) U` is the additive identification of $\Gamma(\mathcal{H}om(M,\mathcal O_X),U)$ with the morphisms $M|_U \to \mathbf{1}|_U$ of restrictions along $U.\iota$, obtained from the natural-families description of sections of the internal Hom; composing the morphism attached to $t$ with the isomorphism `restrictUnitIso' U.ι` from $\mathbf{1}|_U$ to the unit object of $U\text{-Mod}$ yields $\varphi_t \colon M|_U \to \mathcal O_U$, and `coeff s U` evaluates $\varphi_t$ at $\top$ on the restricted section $s.\mathrm{app}\,(U.\iota\,''^{U}\,\top)(1)$ of $M|_U$, transported to $\Gamma(X,U)$ along $U.\mathrm{topIso}$. The theorem asserts that these two elements of $\Gamma(X,U)$ coincide. No hypotheses are imposed on $X$, $M$, $s$, $U$ or $t$.
--
--   This is the compatibility between the abstract functional $s^\vee \colon \mathcal{H}om(M,\mathcal O_X) \to \mathcal O_X$, defined monoidally by precomposition with $s$, and the concrete coefficients $\varphi(s|_U)$ of $s$ along morphisms $\varphi \colon M|_U \to \mathcal O_U$, through which the zero scheme of a section is defined. It is used in the treatment of invertible ideal sheaves and relative effective Cartier divisors, in particular in [`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection`](thm.html#AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection) and in the transfer of the condition of being supported in a closed subscheme across an isomorphism of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.ofUnitSection_sectionDual_app
    {X : Scheme.{u}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    Scheme.Modules.ofUnitSection U ((Scheme.Modules.sectionDual s).app U t) =
      Scheme.Modules.coeff s U
        (Scheme.Modules.ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫
          (Scheme.Modules.restrictUnitIso' U.ι).hom) := by sorry
