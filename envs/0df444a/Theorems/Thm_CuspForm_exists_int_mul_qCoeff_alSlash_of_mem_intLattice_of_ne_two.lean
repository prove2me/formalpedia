-- Prove2me | Theorems.Thm_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
-- name    : CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4c1ba8cf-ab1e-5bb4-95b5-cfebd1a5a53f
-- title:
--   Atkin–Lehner slash at p has denominator dividing p
-- statement:
--   Let $p$ be a natural number that is prime (as a typeclass fact) and assume $p \neq 2$; let $M$ be a nonzero natural number and let $A$ be an Atkin–Lehner datum for $M$ at $p$, that is, a natural number $R$ together with the factorisation $M = p \cdot R$ and integers $a, b$ satisfying the Bézout relation $p a - R b = 1$ (so $p$ and $R$ are coprime, and $p$ exactly divides $M$). Let $f$ be a cusp form of weight $2$ on $\Gamma_0(M)$ which lies in [`CuspForm.intLattice M 2`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb{Z}$-submodule spanned by those weight-$2$ cusp forms on $\Gamma_0(M)$ all of whose $q$-expansion coefficients at width $1$ are rational integers, and let $n$ be a natural number. Then there is an integer $m$ with
--   $$p \cdot \operatorname{qCoeff}\bigl(f \mid_{2} A.\mathrm{alGL}\bigr)(n) = m$$
--   in $\mathbb{C}$, where $f \mid_{2} A.\mathrm{alGL}$ is the weight-$2$ slash of $f$ by the invertible real matrix [`ModularForm.AtkinLehnerDatum.alGL`](def/ModularForm_AtkinLehnerDatum.html#L93) attached to $A$ (the base change to $\mathbb{R}$ of the datum's integral matrix), and $\operatorname{qCoeff}$ takes the $n$-th coefficient of the $q$-expansion of width $1$. Thus the $q$-coefficients of the Atkin–Lehner image of an integral weight-$2$ cusp form have denominator dividing $p$.
--
--   This is the integrality statement for the Atkin–Lehner involution $W_p$ in weight $2$ at a prime exactly dividing the level: on forms with integral $q$-expansion the operator introduces denominators at most $p$, the bound being attained by $p$-oldforms. It is used in the mod $p$ analysis of $q$-expansions of weight-$2$ and weight-$4$ forms that underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2) (n : ℕ) :
    ∃ m : ℤ, (p : ℂ) * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ) := by sorry
