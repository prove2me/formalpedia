-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_subsingleton_of_genusFF_eq_zero
-- name    : AlgebraicCurve.Pic0.subsingleton_of_genusFF_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/76c38892-fce8-5aad-9013-81c0a54d8ec7
-- title:
--   Genus zero forces trivial degree-zero divisor class group
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure which is a curve over $K$ in the project's sense, i.e. `IsCurveOver K F` holds: every nonzero $f \in F$ has an associated divisor, namely a finitely supported function $D$ on the set of places with $D(v) = \operatorname{ord}_v f$ for all $v$ and $\deg D = 0$ (a place being a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring); the residue field of every place is a finite-dimensional $K$-module; and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$. Assume moreover that $F$ is essentially of finite type over $K$, and that $\mathrm{genusFF}\,K\,F = 0$, i.e. the $K$-dimension of the first repartition cohomology group $H^1(0)$ attached to the zero divisor vanishes. Then the group $\mathrm{Pic}^0(K,F)$, defined as the group of divisors of degree zero modulo those principal divisors which have degree zero, is a subsingleton: it has at most one element.
--
--   This is the genus-zero case of the Riemann–Roch theorem for function fields: on a curve of genus zero over an algebraically closed field every divisor of degree zero is principal. It is used in the construction and analysis of models of modular curves, where triviality of $\mathrm{Pic}^0$ of a rational function field lets divisor classes be replaced by explicit functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_subsingleton_of_genusFF_eq_zero.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.Pic0.subsingleton_of_genusFF_eq_zero
    {K : Type} [Field K] [IsAlgClosed K]
    {F : Type} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hg : genusFF K F = 0) :
    Subsingleton (Pic0 K F) := by sorry
