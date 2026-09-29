-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/63a2870e-5be7-5a1c-afca-ad814cb7d80f
-- title:
--   Trivialisation of an algebraically trivial bundle with a section
-- statement:
--   Let $k$ be a field, $X$ a scheme and $x \colon X \to \operatorname{Spec} k$ a morphism which is proper, smooth of relative dimension $1$ and geometrically irreducible. Let $\mathcal V$ be a two-affine open cover of $X$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $L$ be an $\mathcal O_X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the restriction of $L$ to $U$ is isomorphic to the unit module of $U$. Assume $L$ satisfies `IsAlgEquivZero` for $x$: there are a scheme $T'$ and a morphism $h \colon T' \to \operatorname{Spec} k$ which is locally of finite type and geometrically integral, an invertible module $M$ on $X \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$ (morphisms $\operatorname{Spec} k \to T'$ composing with $h$ to the identity), such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module of $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$ (formed with the identity), and the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection. Finally let $s \colon \mathbf 1 \to L$ be a nonzero morphism from the unit module. Then the type of isomorphisms $L \cong \mathbf 1$ is nonempty.
--
--   This is the statement that an invertible sheaf algebraically equivalent to zero on a proper smooth geometrically irreducible curve over a field, admitting a nonzero global section, is trivial — the degree-free form of "a degree-zero line bundle with a section is trivial". It is used in the construction of the degree-zero relative Picard group and of the Abel–Jacobi map for curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h0 : IsAlgEquivZero x L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by sorry
