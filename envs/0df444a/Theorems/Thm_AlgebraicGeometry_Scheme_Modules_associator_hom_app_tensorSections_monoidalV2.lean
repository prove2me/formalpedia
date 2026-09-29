-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.associator_hom_app_tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/c5fb217d-3bef-52a8-8bc8-b8cc7cb8ef14
-- title:
--   Associator on sections of a triple tensor product of module sheaves
-- statement:
--   Let $X$ be a scheme, let $L$, $M$, $N$ be objects of `X.Modules` (sheaves of $\mathcal O_X$-modules), let $U$ be an open subset of $X$, and let $l \in \Gamma(L,U)$, $m \in \Gamma(M,U)$, $n \in \Gamma(N,U)$. Here, for sheaves of modules $A$, $B$ and sections $s \in \Gamma(A,U)$, $t \in \Gamma(B,U)$, the section $\mathtt{tensorSections}\ s\ t \in \Gamma(A \otimes B, U)$ is defined as the image of the pure tensor $s \otimes_{\Gamma(X,U)} t$ in the presheaf tensor product $(A^{\mathrm{val}} \otimes B^{\mathrm{val}})(U)$ under the map `tensorSectionsHom`, namely the unit of the sheafification adjunction for presheaves of modules on $X$ followed by the comparison isomorphism identifying the sheafification of the presheaf tensor product with $A \otimes B$, evaluated at $U$. The assertion is that the component at $U$ of the associator $\alpha_{L,M,N} : (L \otimes M) \otimes N \xrightarrow{\sim} L \otimes (M \otimes N)$ of the monoidal category `X.Modules`, applied to the section $(l \otimes m) \otimes n$ built by two applications of `tensorSections`, equals the section $l \otimes (m \otimes n)$, again built by two applications of `tensorSections`, in $\Gamma(L \otimes (M \otimes N), U)$.
--
--   This is the sectionwise description of the associativity constraint of the tensor product of sheaves of modules on a scheme: on sections that are images of pure tensors the associator behaves like the associativity isomorphism of tensor products of modules. It is the associativity half of the basic calculus of `tensorSections`, used in the treatment of tensor powers, where it supports the compatibility of the addition isomorphism $L^{\otimes a} \otimes L^{\otimes b} \cong L^{\otimes(a+b)}$ with sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.associator_hom_app_tensorSections_monoidalV2
    {X : Scheme.{u}} {L M N : X.Modules} {U : X.Opens} (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (α_ L M N).hom.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (L := L ⊗ M) (M := N)
          (AlgebraicGeometry.Scheme.Modules.tensorSections l m) n) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (L := L) (M := M ⊗ N) l
        (AlgebraicGeometry.Scheme.Modules.tensorSections m n) := by sorry
