-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_exists_zsmul_eq_zero_and_toPic0Pair_eq
-- name    : AlgebraicCurve.GluedPic0.exists_zsmul_eq_zero_and_toPic0Pair_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/96a77484-9da6-53cd-a8e7-623bfc25c40d
-- title:
--   Lifting n-torsion through the glued degree-zero class group
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field that is a $K$-algebra, subject to `HasPrincipalDivisors K F`: every $f \in F$, $f \neq 0$, admits a finitely supported divisor $D$ on the places of $F/K$ (a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring) with $D(v) = \operatorname{ord}_v(f)$ for every place $v$ and $\deg D = 0$. Let $S$ be a finite set of ordered pairs of places such that for each $s \in S$ the structure maps $K \to \kappa(s_1)$ and $K \to \kappa(s_2)$ into the residue fields are surjective. Let $n$ be a natural number and let $y$ be a pair of degree-zero divisor classes, i.e. an element of $\operatorname{Pic}^0(F/K)^2$, the quotient of degree-zero divisors by principal ones, with $(n : \mathbb{Z}) \cdot y = 0$. Then there is an element $x$ of `GluedPic0 K F S` — the quotient of the group of admissible gluing data, namely triples $(D_1, D_2, a)$ with $D_1, D_2$ of degree zero, $D_1(s_1) = D_2(s_2) = 0$ for all $s \in S$, and $a : S \to \operatorname{Additive} K^\times$, by the subgroup of glued-principal data — such that $(n : \mathbb{Z}) \cdot x = 0$ and `toPic0Pair S x = y`, where `toPic0Pair` sends the class of $(D_1, D_2, a)$ to the pair of classes of $D_1$ and $D_2$.
--
--   This is the surjectivity of the projection from the $n$-torsion of a glued (generalised) degree-zero class group onto the $n$-torsion of the product of the two ordinary ones, the glued group playing the role of the Picard group of a curve with the places of $S$ identified in pairs. It is used in the analysis of the Néron model of $J_H$ at $p$, both for the Tate module of $J_H$ and for the description of toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_exists_zsmul_eq_zero_and_toPic0Pair_eq.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.GluedPic0.exists_zsmul_eq_zero_and_toPic0Pair_eq {K F : Type*} [Field K]
    [IsAlgClosed K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hrat : ∀ s ∈ S,
      Function.Surjective (algebraMap K (s.1.ResidueField)) ∧
        Function.Surjective (algebraMap K (s.2.ResidueField)))
    (n : ℕ) (y : AlgebraicCurve.Pic0 K F × AlgebraicCurve.Pic0 K F) (hy : (n : ℤ) • y = 0) :
    ∃ x : AlgebraicCurve.GluedPic0 K F S,
      (n : ℤ) • x = 0 ∧ AlgebraicCurve.GluedPic0.toPic0Pair S x = y := by sorry
