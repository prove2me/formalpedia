-- Prove2me | Theorems.Thm_CuspForm_petersson_conj_symm
-- name    : CuspForm.petersson_conj_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/b8b0992d-4d59-5a28-bb0e-5d5a473583a4
-- title:
--   Conjugate symmetry of the Petersson pairing on Γ₀(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k$ be an integer, and let $f, g$ be cusp forms of weight $k$ for the congruence subgroup $\mathrm{CongruenceSubgroup.Gamma0}\ N \le \mathrm{SL}(2,\mathbb{Z})$. Here [`CuspForm.petersson f g`](def/CuspForm_Petersson.html#L20) denotes the integral, with respect to Lebesgue measure restricted to the fundamental domain `ModularGroup.fd` for the modular group, of the function [`CuspForm.peterssonIntegrand f g`](def/CuspForm_Petersson.html#L16), whose value at $\tau$ in the upper half-plane is the (unconditional) sum over all cosets $q$ in $\mathrm{SL}(2,\mathbb{Z}) / \mathrm{CongruenceSubgroup.Gamma0}\ N$ of the weight-$k$ Petersson density `UpperHalfPlane.petersson k` — the product of the first function with the complex conjugate of the second, weighted by $(\operatorname{Im} \tau)^k$ — evaluated at $\tau$ on the pair of slash-translates $f \mid[k] (q.\mathrm{out})^{-1}$ and $g \mid[k] (q.\mathrm{out})^{-1}$, taken along a choice of representative $q.\mathrm{out}$ of each coset. The assertion is that applying the complex conjugation ring endomorphism `starRingEnd ℂ` to [`CuspForm.petersson g f`](def/CuspForm_Petersson.html#L20) yields [`CuspForm.petersson f g`](def/CuspForm_Petersson.html#L20). No convergence or integrability hypothesis is imposed; the pairing is defined by the above integral in all cases.
--
--   This is the Hermitian (conjugate-)symmetry of the Petersson pairing on cusp forms of weight $k$ on $\Gamma_0(N)$. It is used in the treatment of newforms, for instance in the results identifying a newform by its $q$-expansion coefficients, by its Hecke eigenvalues away from a finite set of primes, and in the vanishing of certain sums of slash-translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_petersson_conj_symm.lean

import Definitions.Def_CuspForm_Petersson

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.petersson_conj_symm {N : ℕ} {k : ℤ} [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    starRingEnd ℂ (CuspForm.petersson g f) = CuspForm.petersson f g := by sorry
