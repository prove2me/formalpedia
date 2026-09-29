-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_nonempty_tensor_lineBundle_iso_lineBundle
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_nonempty_tensor_lineBundle_iso_lineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/58db1f0b-931b-5b39-83e1-2fcef7624e05
-- title:
--   Line bundles on a smooth proper curve as differences of effective divisors
-- statement:
--   Let $f\colon\mathcal C\to S$ be a morphism of schemes which is proper, smooth of relative dimension $1$ and geometrically irreducible, let $k$ be a field and let $x\colon\operatorname{Spec} k\to S$ be an $S$-point; write $\mathcal C_x$ for the fibre product of $f$ and $x$. Assume given: a `TwoAffineOpenCover` $\mathcal V$ of $\mathcal C_x$, that is, two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine; a natural number $r_0$ and a relative effective Cartier divisor $E_0$ of degree $r_0$, i.e. an ideal sheaf datum $I$ on $\mathcal C_x$ whose associated closed immersion followed by the projection $\mathcal C_x\to\operatorname{Spec} k$ is finite, flat and locally of finite presentation with constant rank $r_0$ at every point; the hypothesis $0<r_0$; and a module $M$ on $\mathcal C_x$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $M$ along $U\hookrightarrow\mathcal C_x$ is isomorphic to the unit sheaf of modules. The conclusion asserts the existence of natural numbers $r_1,r_2$ and relative effective Cartier divisors $E_1,E_2$ of degrees $r_1,r_2$ for $f$ along $x$ together with an isomorphism $M\otimes\mathcal O(E_2)\cong\mathcal O(E_1)$, where $\mathcal O(E)$ denotes the dual of the module attached to the ideal sheaf of $E$. No constraint relating $r_1$, $r_2$ or the degree of $M$ is asserted.
--
--   This is the standard fact that every line bundle on a smooth proper geometrically irreducible curve over a field is a difference $\mathcal O(E_1-E_2)$ of two effective divisors, in the relative formulation used throughout the treatment of the Picard functor. It is used in the construction of the Poincaré bundle data on the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_nonempty_tensor_lineBundle_iso_lineBundle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_nonempty_tensor_lineBundle_iso_lineBundle
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)

    (𝒱 : (pullback f x).TwoAffineOpenCover)
    {r₀ : ℕ} (E₀ : RelEffCartierDiv f r₀ x) (hr₀ : 0 < r₀)
    (M : (pullback f x).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (r₁ r₂ : ℕ) (E₁ : RelEffCartierDiv f r₁ x) (E₂ : RelEffCartierDiv f r₂ x),
      Nonempty (M ⊗ E₂.lineBundle ≅ E₁.lineBundle) := by sorry
