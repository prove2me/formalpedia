-- Prove2me | Theorems.Thm_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice
-- name    : CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/8d80856e-d16b-5a39-a5de-c148a90d9ec8
-- title:
--   Denominator at most p for Wₚ on integral weight-two cusp forms
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $M$ be a nonzero natural number, and let $A$ be an Atkin–Lehner datum for $M$ at $p$, that is, a natural number $R$ together with the factorisation $M = pR$ and integers $a,b$ satisfying $pa - Rb = 1$. Let $f$ be a cusp form of weight $2$ on $\Gamma_0(M)$ which lies in [`CuspForm.intLattice M 2`](def/CuspForm_IntegralStructure.html#L3), the $\mathbb{Z}$-submodule of weight-$2$ cusp forms on $\Gamma_0(M)$ spanned by those cusp forms all of whose $q$-expansion coefficients (the coefficients of the $q$-expansion of period $1$) are rational integers. Then for every natural number $n$ there is an integer $m$ with $$p \cdot \mathrm{qCoeff}\big(\mathrm{alSlash}\,A\,2\,f\big)(n) = m$$ in $\mathbb{C}$, where $\mathrm{alSlash}\,A\,2\,f$ is the weight-$2$ (determinant-normalised) slash of $f$ by the element `A.alGL` of $GL_2(\mathbb{R})$ attached to the datum, namely the image of the datum's integral matrix under $\mathbb{Z} \to \mathbb{R}$, and $\mathrm{qCoeff}$ denotes the $n$-th coefficient of the period-$1$ $q$-expansion. Thus the $q$-coefficients of $f \mid_2 W_p$ lie in $p^{-1}\mathbb{Z}$.
--
--   This is the integrality statement that the Atkin–Lehner involution $W_p$ at a prime $p \ge 5$ exactly dividing the level has denominator dividing $p$ on the lattice of weight-$2$ cusp forms with integral $q$-expansion; the factor $p$ cannot be improved, as the oldform $g(p\,\cdot)$ attached to a form $g$ of level $R$ shows. It feeds the mod $p$ comparison of spaces of cusp forms used in the level-lowering step, being cited by [`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two`](thm.html#ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_IntegralStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2) (n : ℕ) :
    ∃ m : ℤ, (p : ℂ) * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ) := by sorry
