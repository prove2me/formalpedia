-- Prove2me | Theorems.Thm_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
-- name    : CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/fedf84be-4e86-5ee2-b55a-d7ee0e4512fa
-- title:
--   Uᵣ-eigenvalues are roots of X²-aᵣ(g₀)X+r
-- statement:
--   Let $N\ge 1$ and let $r$ be a prime with $r\nmid N$, let $S$ be a finite set of natural numbers, and let $M_0$ be a divisor of $N$. Let $g_0$ be a weight-two cusp form on $\Gamma_0(M_0)$ that is a newform in the project's sense: writing $a_n(g) = \mathrm{qCoeff}\,g\,n$ for the $n$-th coefficient of the $q$-expansion of width $1$, $g_0$ is a normalised eigenform ($a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m,n$, $a_{p^{k+2}} = a_p a_{p^{k+1}} - p\,a_{p^k}$ for primes $p \nmid M_0$ and $a_{p^{k+2}} = a_p a_{p^{k+1}}$ for $p \mid M_0$), and no proper divisor $M$ of $M_0$ carries a normalised eigenform of weight two on $\Gamma_0(M)$ whose coefficients at the primes not dividing $M_0$ agree with those of $g_0$. Let $f \neq 0$ be a weight-two cusp form on $\Gamma_0(Nr)$ such that $T_\ell f = a_\ell(g_0)\, f$ for every prime $\ell \nmid Nr$ outside $S$, where $T_\ell$ is the weight-two Hecke operator given by the sum of slash actions $\sum_{j<\ell} f\mid \mathrm{heckeMatrix}\,\ell\,j + f \mid \mathrm{heckeDiagMatrix}\,\ell$, and such that $U_r f = u\, f$ for some $u \in \mathbb{C}$, with $U_r$ given by $\sum_{j<r} f \mid \mathrm{heckeMatrix}\,r\,j$. Then $u^2 - a_r(g_0)\, u + r = 0$.
--
--   This is the Atkin–Lehner description of the $r$-old space at a prime $r$ exactly dividing the level: the eigenvalues of $U_r$ on the $r$-old part attached to a newform $g_0$ of level prime to $r$ are the two roots of $X^2 - a_r(g_0)X + r$, and the hypothesis tolerates a finite exceptional set $S$ of primes at which no eigenvalue condition is imposed. It is used in the analysis of the auxiliary prime (level raising and the Taylor–Wiles argument), and is cited by [`CohCarrier.eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne`](thm.html#CohCarrier.eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hrN : ¬ r ∣ N) (S : Finset ℕ)
    (M₀ : ℕ) (hM₀N : M₀ ∣ N)
    (g₀ : CuspForm (CongruenceSubgroup.Gamma0 M₀) 2) (hg₀ : g₀.IsNewform)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) (hf : f ≠ 0)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNr : ¬ ℓ ∣ N * r), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓNr f = ModularFormClass.qCoeff g₀ ℓ • f)
    (u : ℂ)
    (hu : haveI : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) hr.ne_zero⟩
      CuspForm.heckeULin 2 (dvd_mul_left r N) f = u • f) :
    u ^ 2 - ModularFormClass.qCoeff g₀ r * u + r = 0 := by sorry
