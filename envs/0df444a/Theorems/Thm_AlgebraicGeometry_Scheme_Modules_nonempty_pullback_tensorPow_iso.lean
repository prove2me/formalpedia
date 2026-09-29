-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/14743d86-f867-585e-a383-9c4a4062e9f4
-- title:
--   Pullback commutes with tensor powers of 𝒪-modules
-- statement:
--   Let $X$ and $Y$ be schemes in a fixed universe, let $f : X \to Y$ be a morphism of schemes, let $L$ be an object of the category $Y.\mathrm{Modules}$ of sheaves of $\mathcal O_Y$-modules, and let $n$ be a natural number. Here $\mathrm{tensorPow}$ is defined by recursion on the exponent in the monoidal category of module sheaves on a scheme: $L.\mathrm{tensorPow}\,0$ is the monoidal unit $\mathbb 1$ of $Y.\mathrm{Modules}$, and $L.\mathrm{tensorPow}\,(n+1) = (L.\mathrm{tensorPow}\,n) \otimes L$; the same recursion is applied on $X$ to the pullback of $L$. The assertion is that the type of isomorphisms in $X.\mathrm{Modules}$ between the image of $L.\mathrm{tensorPow}\,n$ under the pullback functor `Scheme.Modules.pullback f` and the $n$-th tensor power of the pullback of $L$ is nonempty, i.e. that some isomorphism $f^*(L^{\otimes n}) \cong (f^*L)^{\otimes n}$ exists. The statement records existence only; no particular isomorphism is named in the conclusion, and no compatibility with the monoidal structure beyond existence is asserted.
--
--   This is the standard fact that inverse image of $\mathcal O$-modules, being monoidal, commutes with tensor powers, in the weak form of existence of an isomorphism. It is used in the relative Picard part of the development, where tensor powers of a line bundle on a family must be compared with tensor powers of its restriction along a base change, for instance to a closed fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj L).tensorPow n) := by sorry
