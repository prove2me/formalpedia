-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/ab9de863-ad51-5202-b12f-c337ec561c0d
-- title:
--   Nonzero section of a line bundle is nonzero at the generic point
-- statement:
--   Let $X$ be a scheme that is integral, and let $M$ be an $\mathcal{O}_X$-module on $X$ (an object of `X.Modules`) which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules over the sheaf of rings of $U$. Let $s \colon \mathbb{1}_{X\text{-Mod}} \to M$ be a morphism from the monoidal unit (the structure sheaf viewed as a module) to $M$, that is, a global section of $M$, and assume $s \neq 0$. The conclusion is that the generic point of $X$ does not lie in the support of the ideal sheaf datum `Scheme.Modules.zeroSchemeIdeal s`, which by definition is the infimum of all ideal sheaf data $J$ on $X$ with the property that for every affine open $U$ of $X$ the ideal `coeffIdeal s U`, namely the ideal of $\Gamma(X, U)$ spanned by the range of `coeff s U`, is contained in the ideal $J$ assigns to $U$.
--
--   This is the statement that the zero scheme of a nonzero section of a line bundle on an integral scheme is a proper closed subscheme: it misses the generic point. It is used in the construction of relative effective Cartier divisors from nonzero sections, in the frame lemma for third tensor powers, and in the analysis of two glued projective lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal.lean

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    genericPoint X ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by sorry
