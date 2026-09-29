-- Prove2me | Theorems.Thm_CuspForm_petersson_smul_left
-- name    : CuspForm.petersson_smul_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/4ffb387c-321b-5d1d-85af-6811ed1ce143
-- title:
--   Petersson pairing is conjugate-linear in its first argument
-- statement:
--   Fix a level $N \in \mathbb{N}$ with $N \neq 0$ and a weight $k \in \mathbb{Z}$, let $c \in \mathbb{C}$ be a scalar, and let $f, g$ be cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}(2,\mathbb{Z})$. Here the pairing $\langle f, g\rangle =$ [`CuspForm.petersson f g`](def/CuspForm_Petersson.html#L20) is defined by integrating, against Lebesgue measure restricted to the standard fundamental domain `ModularGroup.fd` for the action of $\mathrm{SL}(2,\mathbb{Z})$ on the upper half-plane, the function
--   $$\tau \mapsto \sum_{q \in \mathrm{SL}(2,\mathbb{Z})/\Gamma_0(N)} \mathtt{petersson}\,k\,\bigl(f \mid[k]\, q_{\mathrm{out}}^{-1}\bigr)\bigl(g \mid[k]\, q_{\mathrm{out}}^{-1}\bigr)(\tau),$$
--   the finite sum (`finsum`) being taken over the cosets of $\Gamma_0(N)$ in $\mathrm{SL}(2,\mathbb{Z})$, with $q_{\mathrm{out}}$ a chosen representative of $q$, $\mid[k]$ the weight-$k$ slash action, and `UpperHalfPlane.petersson k` the pointwise Petersson density of Mathlib. The assertion is that scaling the first argument by $c$ multiplies the pairing by the complex conjugate of $c$: $\langle c \cdot f, g\rangle = \bar{c}\,\langle f, g\rangle$, conjugation being the ring endomorphism `starRingEnd ℂ`.
--
--   This is one half of the sesquilinearity of the Petersson inner product on $S_k(\Gamma_0(N))$, namely conjugate-linearity in the first variable. It is used in the uniqueness arguments for newforms, including [`CuspForm.IsNewform.eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_forall_qCoeff_eq) and the vanishing statement [`CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero`](thm.html#CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_petersson_smul_left.lean

import Definitions.Def_CuspForm_Petersson

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.petersson_smul_left {N : ℕ} {k : ℤ} [NeZero N]
    (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (c • f) g = starRingEnd ℂ c * CuspForm.petersson f g := by sorry
