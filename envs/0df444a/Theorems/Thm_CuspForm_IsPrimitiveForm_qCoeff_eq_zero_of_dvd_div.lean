-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div
-- name    : CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/4d7e7fe1-7a57-562b-9328-5a5f56be5876
-- title:
--   Vanishing of a_q for primitive forms when q² ∣ M
-- statement:
--   Let $M \ge 1$ and $k \in \mathbb{Z}$, let $q$ be a prime with $q \mid M$ and $q \mid M/q$ (so $q^2 \mid M$), let $\varepsilon'$ be a Dirichlet character modulo $M/q$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$. Write $a_n(h)$ for the $n$-th coefficient `qCoeff` of the $q$-expansion of width $1$ of a form $h$. Assume $g$ is a primitive form with respect to the character $\varepsilon$ modulo $M$ obtained from $\varepsilon'$ by change of level along $(M/q) \mid M$, in the sense that: $g$ is an eigenform with that character, i.e. $a_1(g) = 1$, for every prime $p \nmid M$ and every $n$ one has $a_{pn}(g) + \varepsilon(p)\,p^{k-1}\,a_{n/p}(g)\,[p \mid n] = a_p(g)\,a_n(g)$, for every prime $\ell \mid M$ and every $n$ one has $a_{\ell n}(g) = a_\ell(g)\,a_n(g)$, and $g$ has nebentypus $\varepsilon$; and moreover, for every divisor $M' \mid M$ with $M' \ne M$, the eigenpacket formed by the coefficients $n \mapsto a_n(g)$ together with the character values $p \mapsto \varepsilon(p)$ does not occur at level $M'$, i.e. there is no character $\varepsilon''$ modulo $M'$ and nonzero cusp form $h$ of weight $k$ for $\Gamma_1(M')$ with nebentypus $\varepsilon''$ and a finite set $S$ of naturals such that for all primes $p \notin S$ one has $\varepsilon''(p) = \varepsilon(p)$ and $a_{pn}(h) + \varepsilon''(p)\,p^{k-1}\,a_{n/p}(h)\,[p \mid n] = a_p(g)\,a_n(h)$ for all $n$. The conclusion is $a_q(g) = 0$.
--
--   This is the vanishing assertion of Li's Theorem 3 (iii) — the case of trivial character being Theorem 3 of Atkin and Lehner: a primitive form whose nebentypus is induced from level $M/q$ has vanishing $q$-th Fourier coefficient as soon as $q^2 \mid M$. It feeds the divisibility statement [`CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`](thm.html#CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq) used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div
    (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    ModularFormClass.qCoeff g q = 0 := by sorry
