-- Prove2me | Theorems.Thm_CuspForm_exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd
-- name    : CuspForm.exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/d3680eda-a418-5f6f-9239-9daa06e47fa2
-- title:
--   U_q on S₂(Γ₀(N)) killed by X R(X) with R(0)∣ qᵃ
-- statement:
--   Let $N$ be a nonzero natural number and consider weight-two cusp forms on $\Gamma_0(N)$. Assume [`CuspForm.HasIntegralStructure N 2`](def/CuspForm_IntegralStructure.html#L6), that is: the $\mathbb{C}$-span of the $\mathbb{Z}$-submodule [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) — the $\mathbb{Z}$-span of those cusp forms all of whose $q$-expansion coefficients lie in $\mathbb{Z}$ — is the whole space. Let $q$ be a prime dividing $N$, with $q^2 \mid N$ and $q^3 \nmid N$ (the bare divisibility $q \mid N$ is carried along as the witness needed to form the Hecke operator). Then there exist a polynomial $R \in \mathbb{Z}[X]$ and a natural number $a$ such that the constant term $R(0)$ divides $q^{a}$ in $\mathbb{Z}$ (so in particular $R \neq 0$), and such that $U_q \cdot R(U_q) = 0$ as an endomorphism of $S_2(\Gamma_0(N))$, the product being composition of $\mathbb{C}$-linear maps and $R(U_q)$ the image of $R$ under evaluation at $U_q$. Here $U_q =$ [`CuspForm.heckeULin 2 hqN`](def/ModularForm_HeckeOperatorForms.html#L83) is the operator induced on cusp forms by $f \mapsto \sum_{j<q} f \mid_{2} \mathrm{heckeMatrix}\,q\,j$.
--
--   This is the integral form of the Atkin–Lehner–Li description of $U_q$ at a prime exactly dividing $N$ to the second power (as in Darmon–Diamond–Taylor, Lemma 4.4): the annihilating polynomial of $U_q$ may be taken with integer coefficients and constant term dividing a power of $q$. It refines the companion statement [`CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd`](thm.html#CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd), whose annihilating polynomial has complex roots that are algebraic integers with $q$-divisible norm, and it feeds the local analysis of the Hecke action recorded in [`CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd.lean

import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd
    (N : ℕ) [NeZero N] (hint : CuspForm.HasIntegralStructure N 2)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N) :
    ∃ (R : Polynomial ℤ) (a : ℕ), R.eval 0 ∣ (q : ℤ) ^ a ∧
      CuspForm.heckeULin 2 hqN * Polynomial.aeval (CuspForm.heckeULin (N := N) 2 hqN) R = 0 := by sorry
