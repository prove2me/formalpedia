-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2ec3ed19-50e8-5b7c-9803-2af8b645bf2a
-- title:
--   Zero scheme of a nonzero section on a fibre curve
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically irreducible, let $k$ be a field and let $x \colon \operatorname{Spec} k \to S$ be a $k$-point of $S$. On the fibre $\mathcal{C}_x = \mathcal{C} \times_S \operatorname{Spec} k$, let $M$ be a module which is invertible in the sense that every point of $\mathcal{C}_x$ has an open neighbourhood $U$ on which the restriction of $M$ along $U \hookrightarrow \mathcal{C}_x$ is isomorphic to the unit module on $U$, and let $s \colon \mathcal{O} \to M$ be a morphism from the monoidal unit which is nonzero. Then there exist a natural number $r$ and a term $D$ of `RelEffCartierDiv f r x`, that is, an ideal sheaf datum $D.I$ on $\mathcal{C}_x$ such that the composite of the closed immersion of the associated closed subscheme with $\mathcal{C}_x \to \operatorname{Spec} k$ is finite, flat and locally of finite presentation with fibrewise rank equal to $r$ at every point of $\operatorname{Spec} k$, whose ideal $D.I$ equals `Scheme.Modules.zeroSchemeIdeal s`, the infimum of all ideal sheaf data $J$ on $\mathcal{C}_x$ with $\operatorname{span}(\operatorname{range}(\mathrm{coeff}\, s\, U)) \le J.\mathrm{ideal}\, U$ for every affine open $U$.
--
--   This is the statement that the scheme of zeros of a nonzero section of a line bundle on a proper smooth geometrically irreducible curve over a field is a relative effective Cartier divisor over that field. It feeds the comparison between such divisors and Euler characteristics, and the construction of isomorphisms between line bundles and divisor bundles, in the development of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper.lean

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = Scheme.Modules.zeroSchemeIdeal s := by sorry
