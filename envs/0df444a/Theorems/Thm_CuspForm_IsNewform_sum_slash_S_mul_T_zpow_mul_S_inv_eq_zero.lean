-- Prove2me | Theorems.Thm_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
-- name    : CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/5ab3358b-9521-5ed8-8348-10ab7a433789
-- title:
--   Trace of a weight-2 newform vanishes when q² ∣ R
-- statement:
--   Let $R$, $R_0$ and $q$ be natural numbers with $R \neq 0$, and let $g$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(R)$. Assume $g$ is a newform in the sense of the project: its $q$-expansion coefficients satisfy $a_1(g) = 1$, $a_{mn}(g) = a_m(g)a_n(g)$ for coprime $m,n$, the recursion $a_{p^{r+2}}(g) = a_p(g)a_{p^{r+1}}(g) - p\,a_{p^r}(g)$ at primes $p \nmid R$ and $a_{p^{r+2}}(g) = a_p(g)a_{p^{r+1}}(g)$ at primes $p \mid R$; and, for every proper divisor $M$ of $R$, there is no normalised eigenform of weight $2$ on $\Gamma_0(M)$ (normalised in the same sense) whose $\ell$-th coefficient agrees with that of $g$ for all primes $\ell \nmid R$. Assume further that $q$ is prime, that $q R_0 = R$ and that $q \mid R_0$ (so $q^2 \mid R$). Then the function $$\sum_{j=0}^{q-1} g \bigm|_2 \bigl(S\, T^{-R_0 j}\, S^{-1}\bigr)$$ on the upper half-plane is identically zero, where the weight-$2$ slash action is applied to the underlying function of $g$, and $S$, $T$ are the standard generators of $\mathrm{SL}_2(\mathbb{Z})$, so that $S T^{-c} S^{-1} = \begin{pmatrix} 1 & 0 \\ c & 1\end{pmatrix}$.
--
--   Since $q \mid R_0$, the lower unipotent matrices $\begin{pmatrix}1&0\\R_0 j&1\end{pmatrix}$ for $0 \le j < q$ represent the cosets of $\Gamma_0(R)$ in $\Gamma_0(R_0)$, so the displayed sum is the trace of $g$ from level $R$ to level $R_0$; the assertion is the vanishing of this trace for a newform of exact level $R$. It is used in the level-lowering part of the argument, by [`CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span`](thm.html#CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm MatrixGroups in

theorem CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
    {R R₀ q : ℕ} [NeZero R]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hg : CuspForm.IsNewform g)
    (hq : q.Prime) (hqR : q * R₀ = R) (hqR₀ : q ∣ R₀) :
    ∑ j ∈ Finset.range q,
      (⇑g) ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((R₀ * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
        = 0 := by sorry
