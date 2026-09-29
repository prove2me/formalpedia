-- Prove2me | Theorems.Thm_CuspForm_petersson_add_left
-- name    : CuspForm.petersson_add_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/95bc8f38-4222-5d54-85cb-c6d8fd3611f7
-- title:
--   Additivity of the Petersson pairing in the first variable
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $k$ be an integer, and let $f_1$, $f_2$, $g$ be cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$ (elements of `CuspForm (CongruenceSubgroup.Gamma0 N) k`). Here [`CuspForm.petersson f g`](def/CuspForm_Petersson.html#L20) is the complex number obtained by integrating, against Lebesgue measure restricted to the standard fundamental domain `ModularGroup.fd` for $\mathrm{SL}_2(\mathbb{Z})$ acting on the upper half-plane, the function [`CuspForm.peterssonIntegrand f g`](def/CuspForm_Petersson.html#L16), whose value at $\tau$ is the (unconditional) sum over the coset space $\mathrm{SL}(2,\mathbb{Z}) / \Gamma_0(N)$ of the pointwise weight-$k$ Petersson densities `UpperHalfPlane.petersson k (f ∣[k] q.out⁻¹) (g ∣[k] q.out⁻¹) τ`, each coset $q$ being evaluated through a chosen representative `q.out` and the weight-$k$ slash action of its inverse. The assertion is the identity $\langle f_1 + f_2, g\rangle = \langle f_1, g\rangle + \langle f_2, g\rangle$ for this pairing, i.e. additivity of [`CuspForm.petersson`](def/CuspForm_Petersson.html#L20) in its first argument with the second argument fixed.
--
--   This is the additivity half of the statement that the Petersson inner product on cusp forms of weight $k$ on $\Gamma_0(N)$ is sesquilinear, for the pairing defined by summing the pointwise Petersson density over the cosets of $\Gamma_0(N)$ and integrating over a fundamental domain for the full modular group. It is used in the multiplicity-one arguments for newforms, where a form is shown to vanish by pairing it against a basis, as in [`CuspForm.IsNewform.eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_forall_qCoeff_eq) and [`CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero`](thm.html#CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_petersson_add_left.lean

import Definitions.Def_CuspForm_Petersson

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.petersson_add_left {N : ℕ} {k : ℤ} [NeZero N]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ + f₂) g = CuspForm.petersson f₁ g + CuspForm.petersson f₂ g := by sorry
