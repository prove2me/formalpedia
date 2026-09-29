-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
-- name    : CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/78f51e93-c5c2-50b4-9276-8233151e027d
-- title:
--   Existence of the q-depleted eigenform at level Mq^e
-- statement:
--   Let $M\ge 1$ and let $f$ be a cusp form of weight $2$ for $\Gamma_0(M)$ which is a normalised eigenform in the sense of the project's predicate on $q$-expansion coefficients: writing $a_n(f)$ for the $n$-th coefficient of the $q$-expansion of $f$ of period $1$, one has $a_1(f)=1$, $a_{mn}(f)=a_m(f)a_n(f)$ whenever $m$ and $n$ are coprime, $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)-p\,a_{p^r}(f)$ for every prime $p\nmid M$ and every $r$, and $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)$ for every prime $p\mid M$ and every $r$. Let $q$ be a prime and $e\ge 1$ an integer, subject to the further condition that $e\ge 2$ in case $q\nmid M$. Then there exists a cusp form $g$ of weight $2$ for $\Gamma_0(Mq^e)$ which is again a normalised eigenform in the same sense (the prime-power recursions now being taken with respect to the level $Mq^e$), and whose $q$-expansion coefficients are given, for every $n\in\mathbb{N}$, by $a_n(g)=0$ if $q\mid n$ and $a_n(g)=a_n(f)$ otherwise; in particular the constant term of $g$ vanishes.
--
--   This is the passage from a normalised weight-two eigenform to its $q$-depletion $f-V_qU_qf$, the oldform at level $Mq^e$ annihilated by $U_q$, in the Atkin–Lehner–Li theory of oldforms. It is used in the step that replaces an eigenform by one whose $q$-th coefficient is a prescribed root of the relevant Hecke polynomial, namely [`CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root`](thm.html#CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
    {M : ℕ} [NeZero M] {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime) (e : ℕ) (he : 1 ≤ e)
    (he2 : ¬ q ∣ M → 2 ≤ e) [NeZero (M * q ^ e)] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * q ^ e)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by sorry
