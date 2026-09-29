-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
-- name    : CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/5bbcb0d1-90c5-548b-964a-31fdb560e07f
-- title:
--   Divisibility of M₂ by powers of q when q² ∣ M₁
-- statement:
--   Let $M_1,M_2\ge 1$ be integers and $k$ an integer, let $\varepsilon_1$ be a Dirichlet character modulo $M_1$ with values in $\mathbb{C}$ and $\varepsilon_2$ one modulo $M_2$, and let $g_1\in S_k(\Gamma_1(M_1))$, $g_2\in S_k(\Gamma_1(M_2))$ be cusp forms. Write $a_n(f)$ for the $n$-th coefficient of the $q$-expansion of $f$ of width $1$. Assume that each $g_i$ is a primitive form of nebentypus $\varepsilon_i$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38): $a_1(g_i)=1$; for every prime $p\nmid M_i$ and every $n$, $a_{pn}(g_i)+\varepsilon_i(p)p^{k-1}\,[\,p\mid n\,]\,a_{n/p}(g_i)=a_p(g_i)a_n(g_i)$; for every prime $\ell\mid M_i$ and every $n$, $a_{\ell n}(g_i)=a_\ell(g_i)a_n(g_i)$; the predicate [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) holds for $\varepsilon_i$ and $g_i$; and for no divisor $M'\ne M_i$ of $M_i$ does the eigenpacket $\bigl(n\mapsto a_n(g_i),\;n\mapsto\varepsilon_i(n)\bigr)$ occur at level $M'$, i.e. there is no character $\varepsilon'$ modulo $M'$ and nonzero $h\in S_k(\Gamma_1(M'))$ with `HasNebentypus` $\varepsilon'$ $h$ and a finite set $S$ of naturals such that for all primes $p\notin S$ one has $\varepsilon'(p)=\varepsilon_i(p)$ and $a_{pn}(h)+\varepsilon'(p)p^{k-1}\,[\,p\mid n\,]\,a_{n/p}(h)=a_p(g_i)a_n(h)$ for all $n$. Assume further that $a_n(g_1)=a_n(g_2)$ and $\varepsilon_1(n)=\varepsilon_2(n)$ for every $n$ coprime to both $M_1$ and $M_2$, and let $q$ be a prime with $q^2\mid M_1$ such that $\varepsilon_1$ factors through $M_1/q$. Then for every $j$ with $q^j\mid M_1$ one has $q^j\mid M_2$.
--
--   This is the case $q^2 \mid M_1$ with $\varepsilon_1$ of conductor dividing $M_1/q$ in the comparison of levels of two primitive forms whose Hecke eigenvalues and character values agree away from the levels, part of the Atkin–Lehner–Li theory of newforms (strong multiplicity one across levels). It is used in the proof of [`CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq`](thm.html#CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq), which concludes that the two levels and the two forms coincide.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ := by sorry
