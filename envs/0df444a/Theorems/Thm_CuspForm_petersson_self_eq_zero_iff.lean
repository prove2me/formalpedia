-- Prove2me | Theorems.Thm_CuspForm_petersson_self_eq_zero_iff
-- name    : CuspForm.petersson_self_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/edf3d9b4-507c-5393-a64a-cd8024b5a3b9
-- title:
--   Vanishing of the Petersson norm characterises the zero cusp form
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k$ be an integer, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$. The quantity [`CuspForm.petersson f f`](def/CuspForm_Petersson.html#L20) is, by definition, the integral over the standard fundamental domain `ModularGroup.fd` for the full modular group, with respect to Lebesgue measure on the upper half-plane restricted to that domain, of the function sending $\tau$ to the unconditional sum, over the cosets $q$ of $\mathrm{SL}(2,\mathbb{Z}) \,/\, \Gamma_0(N)$, of the pointwise weight-$k$ Petersson density `UpperHalfPlane.petersson k` evaluated at $\tau$ on the pair consisting of the weight-$k$ slash $f \mid[k] (q.\mathrm{out})^{-1}$ with itself, where $q.\mathrm{out}$ denotes a chosen representative of the coset $q$. The theorem asserts the equivalence: this complex number is $0$ if and only if $f$ is the zero cusp form.
--
--   This is the definiteness half of the statement that the Petersson product is a positive-definite Hermitian pairing on the space of cusp forms of weight $k$ on $\Gamma_0(N)$; the coset sum and the integral over a fundamental domain for $\mathrm{SL}_2(\mathbb{Z})$ together compute the usual integral over a fundamental domain for $\Gamma_0(N)$. It is used to separate cusp forms by their Petersson products, and thence in the uniqueness statements for newforms, such as [`CuspForm.IsNewform.eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_forall_qCoeff_eq) and [`CuspForm.IsNewform.eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_isNormalizedEigenform_forall_prime_notMem_qCoeff_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_petersson_self_eq_zero_iff.lean

import Definitions.Def_CuspForm_Petersson

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.petersson_self_eq_zero_iff {N : ℕ} {k : ℤ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = 0 ↔ f = 0 := by sorry
