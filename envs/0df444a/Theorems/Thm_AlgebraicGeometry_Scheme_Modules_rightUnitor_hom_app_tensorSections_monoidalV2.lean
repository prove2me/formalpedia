-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/0c609adf-c880-5c93-a376-db559b3ff0e5
-- title:
--   Right unitor on sections: n⊗ g↦ g n
-- statement:
--   Let $X$ be a scheme, let $N$ be a sheaf of $\mathcal{O}_X$-modules on $X$ (an object of `X.Modules`), let $U$ be an open of $X$, and let $n\in\Gamma(N,U)$ and $g\in\Gamma(X,U)$ be sections of $N$ and of the structure sheaf over $U$. Take the monoidal unit $\mathbf{1}$ of `X.Modules`, whose sections over $U$ are $\Gamma(X,U)$, so that $g$ is a section of $\mathbf{1}$ over $U$, and form the section `tensorSections n g` of $N\otimes\mathbf{1}$ over $U$: by definition this is the image of the elementary tensor $n\otimes_{\Gamma(X,U)}g$ in the presheaf tensor product $(N^{\mathrm{val}}\otimes\mathbf{1}^{\mathrm{val}})(U)$ under the map `tensorSectionsHom`, namely the unit of the sheafification adjunction for $\mathcal{O}_X$-modules followed by the comparison isomorphism `tensorIsoSheafify` identifying the sheafification of the presheaf tensor product with the monoidal product $N\otimes\mathbf{1}$ in `X.Modules`. The assertion is that the component at $U$ of the right unitor $\rho_N\colon N\otimes\mathbf{1}\xrightarrow{\ \sim\ }N$ sends this section to $g\cdot n\in\Gamma(N,U)$.
--
--   This is the sectionwise description of the right unitor for the monoidal structure on sheaves of modules over a scheme, in the form needed to compute with elementary tensors of sections. It is used in the computation of section algebras such as $\bigoplus_n\Gamma(X,\mathcal{L}^{\otimes n})$ for an invertible sheaf, and is cited here by the compatibility of `tensorPowAdd` with tensor powers of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections_monoidalV2
    {X : Scheme.{u}} {N : X.Modules} {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n := by sorry
