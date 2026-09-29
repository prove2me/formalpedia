-- Prove2me | Theorems.Thm_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
-- name    : CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/b29a720c-712c-564e-be2e-f7cd7edb33c5
-- title:
--   Annihilating polynomial for U_q when q² exactly divides N
-- statement:
--   Let $N$ be a nonzero natural number and let $q$ be a prime with $q \mid N$, $q^2 \mid N$ and $q^3 \nmid N$. Write $U_q$ for the $\mathbb{C}$-linear endomorphism [`CuspForm.heckeULin 2 hqN`](def/ModularForm_HeckeOperatorForms.html#L83) of the space $S_2(\Gamma_0(N))$ of weight-two cusp forms for $\Gamma_0(N)$, the operator induced on cusp forms by $f \mapsto \sum_{j<q} f \mid_{[2]} \mathrm{heckeMatrix}(q,j)$, the sum of the weight-two slash actions of the matrices $\mathrm{heckeMatrix}(q,j)$ for $0 \le j < q$. The assertion is that there exists a polynomial $Q \in \mathbb{C}[X]$ with two properties: first, every complex root $\mu$ of $Q$ is integral over $\mathbb{Z}$ and divides $q$ in the algebraic integers, that is, there is a $\nu \in \mathbb{C}$ integral over $\mathbb{Z}$ with $\mu\nu = q$; second, $U_q \circ Q(U_q) = 0$ in the endomorphism ring of $S_2(\Gamma_0(N))$, where $Q(U_q)$ is the evaluation of $Q$ at $U_q$. Thus the polynomial $X \cdot Q(X)$ annihilates $U_q$ on $S_2(\Gamma_0(N))$. Nothing is asserted about the degree of $Q$, nor explicitly that $Q \neq 0$ (which nevertheless follows from the condition on its roots).
--
--   This is the Atkin–Lehner–Li description of the action of $U_q$ on the full space of weight-two cusp forms at a prime dividing the level exactly to order two, in the form used by Darmon–Diamond–Taylor (Lemma 4.4): $U_q$ satisfies a polynomial $X\cdot Q(X)$ whose nonzero roots are algebraic integers dividing $q$. It is cited by [`CuspForm.exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd`](thm.html#CuspForm.exists_heckeULin_mul_aeval_eq_zero_of_sq_dvd_of_not_cube_dvd), which records the same annihilation statement without the integrality information.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N) :
    ∃ Q : Polynomial ℂ,
      (∀ μ : ℂ, Q.IsRoot μ → IsIntegral ℤ μ ∧ ∃ ν : ℂ, IsIntegral ℤ ν ∧ μ * ν = q) ∧
      CuspForm.heckeULin 2 hqN * Polynomial.aeval (CuspForm.heckeULin (N := N) 2 hqN) Q = 0 := by sorry
