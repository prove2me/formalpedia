-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase
-- name    : AlgebraicCurve.GluedPic0.nodeUnit_eq_zero_iff_of_constantsAreBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/849eafb0-34ba-5ed3-907a-2cb6c7e154ee
-- title:
--   Node units vanish in GluedPic⁰ only for constants
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `ConstantsAreBase K F`, i.e. that the Riemann–Roch space `LSpace (0 : Divisor K F)` of the zero divisor, a $K$-submodule of $F$, coincides with the range of the $K$-algebra map $K \to F$. Let $S$ be a finite set of ordered pairs of places of $F/K$, a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring, and let $w : S \to \mathrm{Additive}\,K^\times$ assign to each pair in $S$ a unit of $K$, written additively. Here gluing data are triples consisting of two divisors (finitely supported $\mathbb{Z}$-valued functions on places) and such a function $w$; such a triple is admissible when both divisors have degree zero and, for every $s \in S$, the first divisor vanishes at the first place of $s$ and the second divisor vanishes at the second place of $s$; `GluedPic0 K F S` is the quotient of the group of admissible data by the subgroup of those satisfying `IsGluedPrincipal`, and `nodeUnit S w` is the class of the admissible triple $(0,0,w)$. The assertion is that `nodeUnit S w` vanishes in `GluedPic0 K F S` if and only if there is a unit $c \in K^\times$ with $w$ the constant function with value $c$ (transported into the additive copy of $K^\times$).
--
--   This identifies the kernel of the map sending a node-gluing datum to its class in the glued degree-zero divisor class group: over a curve whose constants are exactly $K$, the only gluing data that are trivial in $\mathrm{GluedPic}^0$ are the diagonal ones. It is used in the analysis of the kernel of the map from $\mathrm{GluedPic}^0$ to the pair of ordinary degree-zero class groups, in particular in `eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero`, `eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero` and the count `natCard_ker_toPic0Pair_inf_torsionBy`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase.lean

import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.GluedPic0.nodeUnit_eq_zero_iff_of_constantsAreBase
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F)) (w : ↥S → Additive Kˣ) :
    nodeUnit S w = 0 ↔ ∃ c : Kˣ, w = fun _ => Additive.ofMul c := by sorry
