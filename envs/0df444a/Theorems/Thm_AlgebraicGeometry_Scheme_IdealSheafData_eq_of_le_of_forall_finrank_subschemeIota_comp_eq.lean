-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_le_of_forall_finrank_subschemeIota_comp_eq
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_forall_finrank_subschemeIota_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/3a1a4c31-22e0-5f5d-a76a-4596d163a5dd
-- title:
--   Ideal sheaves with equal relative rank coincide
-- statement:
--   Let $X$ and $S$ be schemes and $p : X \to S$ a morphism, and let $I$ and $J$ be two quasi-coherent ideal sheaf data on $X$ with $I \le J$, so that the closed subscheme cut out by $J$ is contained in the one cut out by $I$. Write $\iota_I$ and $\iota_J$ for the closed immersions `I.subschemeι` and `J.subschemeι` of these closed subschemes into $X$. Assume that the composite $\iota_I$ followed by $p$ is finite, flat and locally of finite presentation over $S$, and that the composite $\iota_J$ followed by $p$ is flat and locally of finite presentation over $S$. Assume finally that for every point $s$ of $S$ the ranks agree: the value of `Scheme.Hom.finrank` at $s$ for the structure morphism of the subscheme of $J$ equals its value at $s$ for the structure morphism of the subscheme of $I$. Then $I = J$ as ideal sheaf data on $X$.
--
--   This is the rank-sandwich principle: a closed subscheme of a finite flat $S$-scheme of finite presentation which is again flat of finite presentation of the same fibre rank everywhere must be the whole thing, phrased here as an equality of the corresponding ideal sheaves. It is used in the theory of Drinfeld level structures, where one identifies the ideal of a Drinfeld divisor $\sum_{a,b<q}[aP+bQ]$ with the ideal of the full $q$-torsion subscheme $E[q]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_le_of_forall_finrank_subschemeIota_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_forall_finrank_subschemeIota_comp_eq
    {X S : Scheme.{u}} (p : X ⟶ S) (I J : X.IdealSheafData) (hIJ : I ≤ J)
    [IsFinite (I.subschemeι ≫ p)] [Flat (I.subschemeι ≫ p)] [LocallyOfFinitePresentation (I.subschemeι ≫ p)]
    [Flat (J.subschemeι ≫ p)] [LocallyOfFinitePresentation (J.subschemeι ≫ p)]
    (h : ∀ s : S, (J.subschemeι ≫ p).finrank s = (I.subschemeι ≫ p).finrank s) :
    I = J := by sorry
