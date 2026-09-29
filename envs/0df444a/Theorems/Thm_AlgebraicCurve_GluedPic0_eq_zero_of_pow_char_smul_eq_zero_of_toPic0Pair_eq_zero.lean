-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
-- name    : AlgebraicCurve.GluedPic0.eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/fbedb34f-f790-5253-b0fa-8cdaf56b2381
-- title:
--   No p-power torsion in the kernel of GPic⁰ → Pic⁰ × Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, and assume `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor coincides with the image of $K$ in $F$ under the structure map. Let $S$ be a finite set of ordered pairs of places of $F$ over $K$ (a place being a proper valuation subring of $F$ containing $K$ whose ring is a principal ideal ring), and assume `hrat`: for each $s \in S$ the structure maps from $K$ to the residue fields of both coordinates $s_1$ and $s_2$ are surjective. Let $p$ be a prime with $\mathrm{char}\,K = p$ and let $k$ be a natural number. Here `GluedPic0 K F S` is the quotient of the group of admissible gluing data — triples $(D_1, D_2, w)$ with $D_1, D_2$ divisors of degree zero, $D_1(s_1) = 0$ and $D_2(s_2) = 0$ for every $s \in S$, and $w : S \to \mathrm{Additive}\,K^\times$ — by the subgroup of those admissible triples that are glued principal, and `toPic0Pair S` is the induced homomorphism sending the class of $(D_1,D_2,w)$ to the pair of divisor classes of $D_1$ and $D_2$ in $\mathrm{Pic}^0$. The assertion is that an element $x$ of `GluedPic0 K F S` with $(p^k : \mathbb{Z}) \cdot x = 0$ and `toPic0Pair S x = 0` is zero.
--
--   The kernel of the pull-back from the glued degree-zero divisor class group to the product of the two copies of $\mathrm{Pic}^0$ is the node-unit torus $(K^\times)^S/K^\times$, which in characteristic $p$ is $p$-divisible without $p$-power torsion; this statement records that the pull-back is injective on $p$-power torsion. It is used in the analysis of the $p$-torsion of the Néron model of the Jacobian of a modular curve at $p$, in [`ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin`](thm.html#ModularCurve.JHNeronObjectAtP.exists_eq_add_pull_add_pull_of_mem_finPts_of_abelJacobiPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.GluedPic0.eq_zero_of_pow_char_smul_eq_zero_of_toPic0Pair_eq_zero
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : Place K F × Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : Place K F × Place K F).2.ResidueField)))
    (p : ℕ) [Fact p.Prime] [CharP K p] (k : ℕ)
    (x : GluedPic0 K F S) (hx : (p ^ k : ℤ) • x = 0) (h0 : GluedPic0.toPic0Pair S x = 0) :
    x = 0 := by sorry
