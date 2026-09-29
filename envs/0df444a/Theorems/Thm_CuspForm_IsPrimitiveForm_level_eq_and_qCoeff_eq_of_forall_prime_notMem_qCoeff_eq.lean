-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
-- name    : CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/544d6a0e-5a27-54a4-8257-87afc9457c4b
-- title:
--   Strong multiplicity one across levels for primitive forms
-- statement:
--   Fix nonzero natural numbers $M_1, M_2$, an integer weight $k$, Dirichlet characters $\varepsilon_1$ modulo $M_1$ and $\varepsilon_2$ modulo $M_2$ with values in $\mathbb{C}$, and cusp forms $g_1$ of weight $k$ for $\Gamma_1(M_1)$ and $g_2$ of weight $k$ for $\Gamma_1(M_2)$; write $a_n(g) =$ [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of width $1$. Assume each $g_i$ is a primitive form with character $\varepsilon_i$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38), namely: $a_1(g_i) = 1$; for every prime $p \nmid M_i$ and every $n$, $a_{pn}(g_i) + \varepsilon_i(p)p^{k-1}\,[p \mid n]\,a_{n/p}(g_i) = a_p(g_i)a_n(g_i)$; for every prime $\ell \mid M_i$ and every $n$, $a_{\ell n}(g_i) = a_\ell(g_i)a_n(g_i)$; $g_i$ has nebentypus $\varepsilon_i$ in the sense of [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13); and for no proper divisor $M'$ of $M_i$ does the eigenpacket $\bigl((a_n(g_i))_n,(\varepsilon_i(n))_n\bigr)$ occur at level $M'$, i.e. there are no character $\varepsilon'$ modulo $M'$, nonzero $h \in S_k(\Gamma_1(M'))$ with nebentypus $\varepsilon'$ and finite set of exceptions outside which, for all primes $p$, $\varepsilon'(p) = \varepsilon_i(p)$ and $a_{pn}(h) + \varepsilon'(p)p^{k-1}\,[p \mid n]\,a_{n/p}(h) = a_p(g_i)a_n(h)$ for all $n$. Assume finally that for some finite set $S$ of naturals, every prime $p \notin S$ satisfies $a_p(g_1) = a_p(g_2)$ and $\varepsilon_1(p) = \varepsilon_2(p)$. The conclusion is $M_1 = M_2$ together with $a_n(g_1) = a_n(g_2)$ for every natural number $n$.
--
--   This is strong multiplicity one across levels: a primitive form is pinned down, level included, by its Hecke eigenvalues and character values at all but finitely many primes. The conclusion is stated as equality of levels and of all $q$-expansion coefficients rather than as an equality $g_1 = g_2$ of forms, which would require the two spaces to be identified first. It is used in the project's comparison of eigenpackets at a level with those at its divisors, and in the analysis of the Hecke eigenspaces attached to newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    M₁ = M₂ ∧ ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n := by sorry
