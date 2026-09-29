-- Prove2me | Theorems.Thm_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
-- name    : CuspForm.exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/f4eee615-c08f-560f-b2bb-502b0229cbf6
-- title:
--   Serre's weight p+1 congruence for Uₚ of a weight-2 form
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $M$ be a nonzero natural number, and let $A$ be an Atkin–Lehner datum for $M$ at $p$, that is, a natural number $R = A.R$ together with a factorisation $M = p\,R$ and integers $a, b$ satisfying $p\,a - R\,b = 1$. Let $f$ be a cusp form of weight $2$ on $\Gamma_0(M)$ belonging to [`CuspForm.intLattice M 2`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb{Z}$-span of those weight-$2$ cusp forms on $\Gamma_0(M)$ all of whose $q$-expansion coefficients (with respect to width $1$) are rational integers. Let $c$ be a natural number with $c + 2 \le p$, and assume that for every $n$ the quantity $p^c$ times the $n$-th $q$-coefficient of [`ModularForm.alSlash A 2 f`](def/ModularForm_AtkinLehnerDatum.html#L141), the weight-$2$ slash of $f$ by the element of $\mathrm{GL}_2(\mathbb{R})$ attached to the datum $A$, is a rational integer. Then there exists $g$ in [`CuspForm.intLattice A.R ((p : ℤ) + 1)`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb{Z}$-span of the weight-$(p+1)$ cusp forms on $\Gamma_0(R)$ with integral $q$-expansion, such that for every $n$ the difference between the $n$-th $q$-coefficient of $g$ and the $n$-th $q$-coefficient of $\sum_{j<p} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & p\end{pmatrix}$ lies in $p\,\mathbb{Z}$.
--
--   This is the congruence form of Serre's observation that a mod $p$ cusp form of weight $2$ and level $pR$ comes from level $R$ in weight $p+1$, here realised by applying $U_p$ to $f$ and matching it modulo $p$ with an integral weight-$(p+1)$ form on $\Gamma_0(R)$. It feeds the comparison of dimensions of spaces of mod $p$ cusp forms used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ p)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (p : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R ((p : ℤ) + 1), ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑f) n = (p : ℂ) * m := by sorry
