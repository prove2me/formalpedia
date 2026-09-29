-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1fba6519-c9a2-56ad-9a98-1de671031b1c
-- title:
--   Tensor powers of a frame are frames
-- statement:
--   Let $X$ be a scheme, let $L$ be an $\mathcal O_X$-module (an object of `X.Modules`), let $U$ and $V$ be open subsets of $X$, and let $s \in \Gamma(L,U)$ be a section of $L$ over $U$. Assume `IsFrameOn s V`, that is: for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X,W) \to \Gamma(L,W)$, $g \mapsto g \cdot (s|_W)$, sending a function to its product with the restriction of $s$ along $W \le U$, is bijective. Then for every natural number $n$ the same holds for the $n$-th tensor power section: `tensorPowSection s n`, an element of $\Gamma(L^{\otimes n}, U)$ defined recursively by $s^{\otimes 0} = \mathrm{unitSection} = 1 \in \Gamma(X,U) = \Gamma(\mathbf 1_{X\text{-Mod}}, U)$ and $s^{\otimes (n+1)} = \mathrm{tensorSections}\,(s^{\otimes n})\, s \in \Gamma(L^{\otimes n} \otimes L, U)$, satisfies `IsFrameOn (tensorPowSection s n) V`: for every open $W \le U$ with $W \le V$, the map $g \mapsto g \cdot (s^{\otimes n}|_W)$ from $\Gamma(X,W)$ to $\Gamma(L^{\otimes n},W)$ is bijective. Here $L^{\otimes n}$ is `tensorPow`, defined by $L^{\otimes 0} = \mathbf 1$ and $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$.
--
--   This is the statement that a trivialising section of a module over an open set trivialises all its tensor powers there: if $s$ is a frame for $L$ on $V$ then $s^{\otimes n}$ is a frame for $L^{\otimes n}$ on $V$. It is used in the treatment of invertible modules and of projective presentations, for instance when comparing sections of $L^{\otimes n}$ with functions and when producing local monomial generators for tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection.lean

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

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by sorry
