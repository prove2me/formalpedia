-- Prove2me | Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero
-- name    : CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/d2513f15-f9da-59fe-a397-50fd0805a212
-- title:
--   Vanishing of Tr(w_qf) forces a_q(f)²=1
-- statement:
--   Let $N$ and $q$ be natural numbers with $N$ nonzero, and let $W$ be an Atkin–Lehner datum at $(N,q)$, that is, a natural number $R=W.R$ together with the factorisation $N=qR$ and integers $a,b$ satisfying $qa-Rb=1$; assume $q$ is prime. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a normalized eigenform in the sense of `IsNormalizedEigenform`: its $q$-expansion coefficients $a_n=$ `qCoeff f n` (coefficients of the width-$1$ $q$-expansion) satisfy $a_1=1$, $a_{mn}=a_ma_n$ for coprime $m,n$, and for every prime $p$ the recursions $a_{p^{r+2}}=a_pa_{p^{r+1}}-p\,a_{p^r}$ when $p\nmid N$ and $a_{p^{r+2}}=a_pa_{p^{r+1}}$ when $p\mid N$. Write $w_2$ for the linear operator `atkinLehnerLin W 2`, given on functions by the weight-$2$ slash action of $W.\mathrm{alGL}$, and `traceLin W hq` for the linear map $g\mapsto g+U_q(w_2 g)$ from weight-$2$ cusp forms on $\Gamma_0(N)$ to weight-$2$ cusp forms on $\Gamma_0(R)$, where $U_q h=\sum_{j<q}h\mid_2\mathrm{heckeMatrix}\,q\,j$. The hypothesis is that `traceLin W hq` applied to $w_2f$ is the zero cusp form. The conclusion is $a_q^2=1$.
--
--   This is the standard criterion identifying the $q$-th coefficient of a weight-$2$ normalized eigenform of level $N=qR$ as $\pm 1$ once the level-lowering trace of its Atkin–Lehner image vanishes; classically it records that such an $f$ is an eigenvector of $w_q$ with eigenvalue $-a_q$, and that this eigenvalue is a sign. It is used in the analysis of $q$-new eigenforms, feeding the statements [`CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne`](thm.html#CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne) and [`CuspForm.exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support`](thm.html#CuspForm.exists_isNormalizedEigenform_isNewAt_of_heckeAlgebra_support).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero.lean

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.qCoeff_sq_eq_one_of_traceLin_atkinLehnerLin_eq_zero {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (h : CuspForm.traceLin W hq (CuspForm.atkinLehnerLin W 2 f) = 0) :
    ModularFormClass.qCoeff f q ^ 2 = 1 := by sorry
