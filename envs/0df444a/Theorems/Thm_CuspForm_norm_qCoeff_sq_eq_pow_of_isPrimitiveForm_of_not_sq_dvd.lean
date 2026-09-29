-- Prove2me | Theorems.Thm_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd
-- name    : CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/e9fbf55f-a80f-502b-a4b3-cae79d8dcfb2
-- title:
--   Li's theorem: |b_ℓ|²=ℓ^{k-2} at an exact level divisor
-- statement:
--   Fix a positive integer $M$ and an integer $k$, a prime $\ell$ with $\ell \mid M$ and $\ell^2 \nmid M$, a Dirichlet character $\varepsilon'$ modulo $M/\ell$ with values in $\mathbb{C}$, and a cusp form $g$ of weight $k$ for $\Gamma_1(M)$. Write $b_n =$ [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $g$ of width $1$, and let $\varepsilon$ be the character modulo $M$ obtained from $\varepsilon'$ by `DirichletCharacter.changeLevel` along $M/\ell \mid M$. The hypothesis is that $g$ is a primitive form with character $\varepsilon$, which by definition means: $g$ is an eigenform with character $\varepsilon$, i.e. $b_1 = 1$; for every prime $p \nmid M$ and every $n$, $b_{pn} + \varepsilon(p)\,p^{k-1}\,b_{n/p}\,[p \mid n] = b_p b_n$ (the third term being $0$ when $p \nmid n$); for every prime $q \mid M$ and every $n$, $b_{qn} = b_q b_n$; and $g$ satisfies the predicate `HasNebentypus` for $\varepsilon$; together with minimality of the level: for every divisor $M'$ of $M$ with $M' \neq M$, the eigenpacket $(n \mapsto b_n,\ n \mapsto \varepsilon(n))$ does not occur at level $M'$, that is, there is no character $\varepsilon''$ modulo $M'$ and no nonzero cusp form $h$ of weight $k$ for $\Gamma_1(M')$ with `HasNebentypus` for $\varepsilon''$ and a finite set $S$ of primes such that for all primes $p \notin S$ one has $\varepsilon''(p) = \varepsilon(p)$ and, for all $n$, the Hecke recursion $c_{pn} + \varepsilon''(p)\,p^{k-1}\,c_{n/p}\,[p \mid n] = b_p\,c_n$ holds for the coefficients $c_n$ of $h$. The conclusion is the equality of real numbers $\lVert b_\ell \rVert^2 = \ell^{\,k-2}$.
--
--   This is the Atkin–Lehner–Li evaluation of the $\ell$-th coefficient of a newform at a prime dividing the level exactly once, under the assumption that the nebentypus is induced from modulus $M/\ell$; classically $b_\ell^2$ is $\ell^{k-2}$ times a root of unity, and only the archimedean absolute value is recorded here. It feeds the comparison of Hecke eigenvalue packets at primes of exact level divisibility used in the level-lowering part of the argument, being cited by [`CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`](thm.html#CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq), [`CuspForm.IsPrimitiveForm.ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor`](thm.html#CuspForm.IsPrimitiveForm.ringHom_rationalHeckeOne_mul_eq_of_dvd_of_not_sq_dvd_of_not_dvd_conductor) and [`CuspForm.norm_qCoeff_sq_le_of_isPrimitiveForm`](thm.html#CuspForm.norm_qCoeff_sq_le_of_isPrimitiveForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd
    (M : ℕ) [NeZero M] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (hℓ2 : ¬ ℓ ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / ℓ)) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓM) ε') g) :
    ‖ModularFormClass.qCoeff g ℓ‖ ^ 2 = (ℓ : ℝ) ^ (k - 2) := by sorry
