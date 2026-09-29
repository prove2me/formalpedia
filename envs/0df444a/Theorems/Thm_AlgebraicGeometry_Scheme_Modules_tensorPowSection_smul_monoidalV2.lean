-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/949d251e-a48b-5e65-b5db-352fa6791ff7
-- title:
--   Homogeneity of degree n of s ↦ s^{⊗ n}
-- statement:
--   Let $X$ be a scheme, let $L$ be an object of `X.Modules`, i.e. a sheaf of $\mathcal O_X$-modules on $X$, let $U$ be an open subset of $X$, and let $g \in \Gamma(X,U)$ and $s \in \Gamma(L,U)$. For a natural number $n$, the section $s^{\otimes n}$ of the $n$-th tensor power $L^{\otimes n}$ over $U$ is the one defined by recursion on $n$: for $n = 0$ it is the section $1 \in \Gamma(X,U)$ of the monoidal unit of `X.Modules`, and for $n+1$ it is obtained from $s^{\otimes n}$ and $s$ by applying the component at $U$ of the canonical map from the presheaf tensor product to the sheaf tensor product to the element $s^{\otimes n} \otimes_{\Gamma(X,U)} s$; here $L^{\otimes 0}$ is the monoidal unit and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. The assertion is the identity $$(g \cdot s)^{\otimes n} = g^{n} \cdot s^{\otimes n}$$ in $\Gamma(L^{\otimes n}, U)$, where the $\Gamma(X,U)$-module structures are those of the sections of $L$ and of $L^{\otimes n}$ over $U$.
--
--   This records that taking $n$-th tensor powers of a section is homogeneous of degree $n$ for the action of the ring of functions on the open set, the basic compatibility needed when comparing local frames $s^{\otimes n}$ and $(gs)^{\otimes n}$ of a tensor power and computing its transition functions as $n$-th powers. It is used in the construction of linear maps from sections of tensor powers of a line bundle on a projective presentation, namely by [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2.lean

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

theorem AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowSection (g • s) n =
      g ^ n • AlgebraicGeometry.Scheme.Modules.tensorPowSection s n := by sorry
