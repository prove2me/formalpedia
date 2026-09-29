-- Prove2me | Theorems.Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
-- name    : CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/474b056a-5234-5d7c-b72a-2ff7a60ba7c7
-- title:
--   Atkin–Lehner–Li dichotomy at p ∥ M with unramified character
-- statement:
--   Let $M \geq 1$ and let $k \in \mathbb{Z}$; let $p$ be a prime with $p \mid M$ and $p^{2} \nmid M$, and let $\varepsilon'$ be a complex Dirichlet character modulo $M/p$. Let $f$ be a cusp form of weight $k$ on $\Gamma_1(M)$ with $f \neq 0$, write $a_n =$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $f$ at $\infty$ (the coefficients of `qExpansion 1 f`), and assume: (i) $f$ has nebentypus the character modulo $M$ obtained from $\varepsilon'$ by change of level along $(M/p) \mid M$, that is, $f(\gamma \cdot \tau) = \varepsilon'(\gamma_{11} \bmod (M/p))\,(\gamma_{10}\tau + \gamma_{11})^{k} f(\tau)$ for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau$ in the upper half-plane; (ii) $a_{pn} = a_p a_n$ for every $n \in \mathbb{N}$ (the coefficient form of $U_p f = a_p f$); (iii) for every prime $\ell \nmid M$ and every $n \in \mathbb{N}$, $a_{\ell n} + \varepsilon'(\ell)\,\ell^{\,k-1}\,[\ell \mid n]\,a_{n/\ell} = a_\ell a_n$ (the coefficient form of $T_\ell f = a_\ell f$). No normalisation $a_1 = 1$ and no condition at the other primes dividing $M$ are imposed. Then at least one of the following holds: either $a_p^{2} = \varepsilon'(p)\,p^{\,k-2}$; or there exists a cusp form $g \neq 0$ of weight $k$ on $\Gamma_1(M/p)$ with nebentypus $\varepsilon'$ (in the same sense, for $\gamma \in \Gamma_0(M/p)$) whose coefficients $b_n$ satisfy $b_{\ell n} + \varepsilon'(\ell)\,\ell^{\,k-1}\,[\ell \mid n]\,b_{n/\ell} = a_\ell b_n$ for every prime $\ell \nmid M$ and every $n \in \mathbb{N}$, the eigenvalue being the coefficient $a_\ell$ of $f$.
--
--   This is the elementary ($q$-expansion) form of the $p$-new/$p$-old dichotomy of Atkin–Lehner and Li at a prime dividing the level exactly once at which the nebentypus is unramified: an eigenform for $U_p$ and for the $T_\ell$ with $\ell \nmid M$ either satisfies the relation $a_p^2 = \varepsilon'(p)p^{k-2}$ forced in the $p$-new case, or admits a nonzero descent to level $M/p$ with the same $T_\ell$-eigenvalues. It feeds the descent step for eigenforms at primes not dividing the conductor of the character and the comparison of levels and coefficients for primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
    (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (Gamma1 M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, ModularFormClass.qCoeff f (p * n) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ModularFormClass.qCoeff f p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (Gamma1 (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff g (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff g n := by sorry
