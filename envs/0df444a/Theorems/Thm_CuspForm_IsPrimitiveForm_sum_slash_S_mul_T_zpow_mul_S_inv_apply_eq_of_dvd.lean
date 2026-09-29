-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd
-- name    : CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/cd0801a2-2f2d-5da6-841e-8fbf04ec4a0c
-- title:
--   Lower-unipotent coset sum of a primitive form at q ∣ M
-- statement:
--   Let $M \ge 1$ and $k \in \mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$ which is a primitive form with character $\varepsilon$: that is, writing $a_n =$ `qCoeff g n` for the $n$-th coefficient of the $q$-expansion of $g$ at width $1$, one has $a_1 = 1$, the Hecke relation $a_{pn} + \varepsilon(p)p^{k-1}[p \mid n]a_{n/p} = a_p a_n$ for all primes $p \nmid M$ and all $n$, the multiplicativity $a_{\ell n} = a_\ell a_n$ for all primes $\ell \mid M$ and all $n$, the nebentypus property `HasNebentypus` for $\varepsilon$, and the minimality condition that for no divisor $M' \mid M$ with $M' \ne M$ does the eigenpacket $(n \mapsto a_n,\ n \mapsto \varepsilon(n))$ occur at level $M'$ in the sense of `EigenpacketOccursAt`. Let $q$ be a prime dividing $M$ and $\tau$ a point of the upper half-plane. Then
--   $$\sum_{j=0}^{q-1}\bigl(g \mid_k S T^{j(M/q)} S^{-1}\bigr)(\tau) = q^{\,1-k}\,\overline{a_q}\; g\bigl(\tau/q\bigr),$$
--   where $S, T$ are the standard generators of $\mathrm{SL}_2(\mathbb{Z})$, so that $S T^{n} S^{-1}$ is the lower unipotent matrix with entry $-n$, the exponent uses the exact natural division $M/q$, and $\tau/q$ is the action on $\tau$ of [`ModularForm.heckeMatrix q 0`](def/ModularForm_HeckeOperator.html#L18), the upper-triangular matrix $\begin{pmatrix}1&0\\0&q\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$.
--
--   This is the Atkin–Lehner–Li evaluation of the trace-type sum over the lower unipotent cosets $S T^{jM/q} S^{-1}$ ($0 \le j < q$) attached to a prime $q$ dividing the level of a primitive form, the right-hand side involving the conjugate eigenvalue $\overline{a_q}$ and the form scaled by $\tau \mapsto \tau/q$. It is used in [`CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`](thm.html#CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq), in the determination of the exact level of a primitive form matching a given system of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((⇑g : UpperHalfPlane → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (M / q : ℕ)) * ModularGroup.S⁻¹ :
            SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) *
          g (ModularForm.heckeMatrix q 0 • τ) := by sorry
