-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul
-- name    : AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c7e41280-91a8-56c9-bad3-8f6cf7f00837
-- title:
--   Homogeneity of degree n of s ↦ s^{⊗ n}
-- statement:
--   Let $X$ be a scheme, let $L$ be a sheaf of $\mathcal{O}_X$-modules on $X$ (an object of `X.Modules`), and let $U$ be an open subset of $X$. For a section $g \in \Gamma(X, U)$ of the structure sheaf, a section $s \in \Gamma(L, U)$, and a natural number $n$, the assertion is an identity in $\Gamma(L^{\otimes n}, U)$, where the tensor power $L^{\otimes n}$ is defined recursively by $L^{\otimes 0} = \mathbf{1}$, the unit of the monoidal category of sheaves of modules, and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, and where `tensorPowSection s n`, written $s^{\otimes n}$, is defined recursively by $s^{\otimes 0} = 1 \in \Gamma(X, U)$ regarded as a section of the unit object and $s^{\otimes (n+1)} = s^{\otimes n} \otimes s$, the latter tensor product of sections over $\Gamma(X, U)$ being pushed into $\Gamma(L^{\otimes n} \otimes L, U)$ along the canonical comparison map. The conclusion is $(g \cdot s)^{\otimes n} = g^{n} \cdot s^{\otimes n}$, the scalar actions being those of $\Gamma(X, U)$ on $\Gamma(L, U)$ and on $\Gamma(L^{\otimes n}, U)$ respectively.
--
--   This records that forming the $n$-th tensor power of a section is homogeneous of degree $n$ for the action of the structure sheaf, so that rescaling a local generator of an invertible sheaf rescales the induced generator of its $n$-th tensor power by the $n$-th power of the scalar. It is used in the construction of linear maps on sections of tensor powers of the twisting sheaves in [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_linearMap_sections_tensorPow_twistObj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowSection (g • s) n =
      g ^ n • AlgebraicGeometry.Scheme.Modules.tensorPowSection s n := by sorry
