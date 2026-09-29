-- Prove2me | Theorems.Thm_CuspForm_exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral
-- name    : CuspForm.exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/39563355-e2b5-5039-aac6-a0043810b70d
-- title:
--   Mod 3 congruence between U₃ f and a weight-4 form
-- statement:
--   Let $M$ be a positive integer and let $A$ be an Atkin–Lehner datum for $M$ at $3$: a natural number $R = A.R$ together with the factorisation $M = 3R$ and integers $a,b$ satisfying $3a - Rb = 1$. Assume there is a prime $q$ dividing $R$ with $q \equiv 2 \pmod 3$. Let $f$ be a weight-$2$ cusp form on $\Gamma_0(M)$ lying in [`CuspForm.intLattice M 2`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb{Z}$-span of those weight-$2$ cusp forms on $\Gamma_0(M)$ all of whose $q$-expansion coefficients (taken at width $1$) are rational integers. Let $c$ be a natural number with $c + 2 \le 3$, and assume that for every $n$ the number $3^c$ times the $n$-th $q$-coefficient of $f \mid_2 A$, the weight-$2$ slash of $f$ by the real invertible matrix attached to the datum, is a rational integer. Then there exists a weight-$4$ cusp form $g$ on $\Gamma_0(R)$, lying in the $\mathbb{Z}$-span of the weight-$4$ cusp forms on $\Gamma_0(R)$ with integral $q$-coefficients, such that for every $n$ the difference of the $n$-th $q$-coefficient of $g$ and the $n$-th $q$-coefficient of $U_3 f = \sum_{j=0}^{2} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & 3\end{pmatrix}$ is $3$ times a rational integer.
--
--   This is the $p = 3$ instance, in congruence form, of Serre's observation that a mod $p$ form of level divisible by $p$ can be realised at level prime to $p$ after raising the weight, the weight-$2$ Eisenstein series of level $q$ playing the role of $E_{p-1}$. It is used in the passage from mod $3$ cusp forms of level $3R$ to mod $3$ cusp forms of weight $4$ and level $R$, namely by [`ModPForms.heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral
    {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M 3) (hq : ∃ q : ℕ, q.Prime ∧ q ∣ A.R ∧ q % 3 = 2)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ 3)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (3 : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R 4, ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 3 ⇑f) n = (3 : ℂ) * m := by sorry
