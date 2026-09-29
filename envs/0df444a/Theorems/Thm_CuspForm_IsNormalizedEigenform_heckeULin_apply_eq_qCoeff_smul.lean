-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul
-- name    : CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/78a00f96-7117-53f4-81ec-a9e0bd713310
-- title:
--   Normalized eigenforms are U_q-eigenvectors at bad primes
-- statement:
--   Let $N$ be a positive natural number and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Write $a_n(f)$ for [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ with respect to the period $1$. Assume `f.IsNormalizedEigenform`, i.e. that the four coefficient conditions hold: $a_1(f)=1$; $a_{mn}(f)=a_m(f)a_n(f)$ whenever $m$ and $n$ are coprime; $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)-p\,a_{p^r}(f)$ for every prime $p\nmid N$ and every $r$; and $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)$ for every prime $p\mid N$ and every $r$. Let $q$ be a prime with $q\mid N$. Then the image of $f$ under [`CuspForm.heckeULin 2 hqN`](def/ModularForm_HeckeOperatorForms.html#L83), the $\mathbb{C}$-linear endomorphism of weight-$2$ cusp forms on $\Gamma_0(N)$ induced by $F\mapsto\sum_{j<q} F\mid[2]\,\mathrm{heckeMatrix}\,q\,j$, equals $a_q(f)\cdot f$. Thus $f$ is an eigenvector of the operator $U_q$ with eigenvalue $a_q(f)$.
--
--   This is the standard statement that a normalized eigenform of weight $2$ on $\Gamma_0(N)$ is an eigenvector for the Atkin–Lehner operator $U_q$ at a prime $q$ dividing the level, with eigenvalue its $q$-th coefficient. It feeds the analysis of newforms and of the local behaviour of Hecke operators at primes dividing the level, being cited by results comparing $T_q$ with $U_q$ for $q^2\mid N$ and by the dichotomy statements at primes exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) :
    CuspForm.heckeULin 2 hqN f = ModularFormClass.qCoeff f q • f := by sorry
