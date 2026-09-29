-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/f8ac214a-d44f-53ad-aadc-21c98ef3ffa0
-- title:
--   Left unitor on sections: λ_N(g⊗ n)=g· n
-- statement:
--   Let $X$ be a scheme, let $N$ be a sheaf of $\mathcal{O}_X$-modules (an object of `X.Modules`), let $U$ be an open of $X$, and let $g \in \Gamma(X,U)$ and $n \in \Gamma(N,U)$; the element $g$ is used directly as a section over $U$ of the monoidal unit $\mathbb{1}$ of `X.Modules`. Form `tensorSections` with $L = \mathbb{1}$ and $M = N$: by definition this is the image of the elementary tensor $g \otimes_{\Gamma(X,U)} n$ lying in $(\mathbb{1}.val \otimes N.val)(U)$, the presheaf-level tensor product evaluated at $U$, under the component at $U$ of `tensorSectionsHom`, namely the unit of the sheafification adjunction for presheaves of modules at $\mathbb{1}.val \otimes N.val$ followed by the image under the forgetful functor to presheaves of modules of the isomorphism `tensorIsoSheafify` identifying the sheafification of the presheaf tensor product with the sheaf-level tensor product $\mathbb{1} \otimes N$. The assertion is that applying the component at $U$ of the left unitor isomorphism $(\lambda_N)_{\mathrm{hom}} \colon \mathbb{1} \otimes N \to N$ to this section yields $g \cdot n$, the scalar action of $g \in \Gamma(X,U)$ on $n \in \Gamma(N,U)$.
--
--   This is the expected description on sections of the left unitor for the tensor product of sheaves of modules on a scheme: the canonical isomorphism $\mathcal{O}_X \otimes_{\mathcal{O}_X} N \cong N$ sends $g \otimes n$ to $gn$. It is used in computations with tensor products of invertible sheaves, for instance in the treatment of `zeroSchemeIdeal` under tensoring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by sorry
