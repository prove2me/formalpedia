-- Prove2me | Theorems.Thm_CuspForm_norm_lt_of_heckeTLin_eq_smul
-- name    : CuspForm.norm_lt_of_heckeTLin_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/8f257101-8616-5cd6-b464-b0616261587c
-- title:
--   Cuspidal T_q-eigenvalues at good primes lie below q+1
-- statement:
--   Fix a natural number $N$ and a cusp form $f$ of weight $2$ for $\Gamma_0(N)$ which is non-zero. Let $q$ be a prime with $q \nmid N$ (so in particular $N \neq 0$, since $q$ divides $0$), and let $a$ be a complex number. The operator in play is [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69), the $\mathbb{C}$-linear endomorphism of the space of cusp forms of weight $k$ for $\Gamma_0(N)$ that sends $f$ to the function $\mathrm{heckeT}\,k\,q\,f = \mathrm{heckeU}\,k\,q\,f + f \mid_k \mathrm{heckeDiagMatrix}\,q$, the sum of the partial Hecke sum $\mathrm{heckeU}$ and the weight-$k$ slash of $f$ by the diagonal matrix attached to $q$; that this function is again holomorphic, $\Gamma_0(N)$-invariant of weight $k$ and vanishing at the cusps is part of the construction. Assume that $f$ is an eigenvector of this operator in weight $k = 2$ with eigenvalue $a$, that is, [`CuspForm.heckeTLin 2 hq hqN f = a • f`](def/ModularForm_HeckeOperatorForms.html#L69). The conclusion is the strict inequality $\lVert a \rVert < q + 1$ between the complex absolute value of $a$ and the real number $q + 1$.
--
--   This is the elementary bound separating the Hecke eigenvalues occurring on the cuspidal part from the Eisenstein eigenvalue $q + 1$ of $T_q$ at a prime $q$ not dividing the level; it is obtained from the self-adjointness of $T_q$ for the Petersson product together with the effect of the operator on $q$-expansion coefficients. It is used in the treatment of newforms, in [`CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span`](thm.html#CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span), and in [`ModularCurve.finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd`](thm.html#ModularCurve.finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_norm_lt_of_heckeTLin_eq_smul.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.norm_lt_of_heckeTLin_eq_smul
    {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) {a : ℂ}
    (ha : CuspForm.heckeTLin 2 hq hqN f = a • f) :
    ‖a‖ < q + 1 := by sorry
